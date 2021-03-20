// Copyright (C) 2021 xq-Tec GmbH

use std::alloc;
use std::cell::Cell;
use std::mem::{align_of, size_of};
use std::ptr::null_mut;
use std::str::from_utf8_unchecked_mut;

use crate::{MapEntry, RawValue};

#[derive(Copy, Clone)]
#[repr(C)]
struct ChunkHeader {
    /// Start of previous
    prev_chunk: *mut ChunkHeader,
    /// Total size of allocated memory (including header).
    alloc_size: usize,
}

/// Frees a chunk and returns a pointer to its predecessor, if any.
unsafe fn destroy_chunk(chunk: *mut ChunkHeader) -> *mut ChunkHeader {
    let ChunkHeader {
        prev_chunk,
        alloc_size,
    } = chunk.read();
    alloc::dealloc(
        chunk as *mut u8,
        alloc::Layout::from_size_align_unchecked(alloc_size, ALIGNMENT),
    );
    prev_chunk
}

const ALIGNMENT: usize = 8;
const HEADER_SIZE: usize = size_of::<ChunkHeader>();

pub struct Arena {
    curr_chunk: Cell<*mut ChunkHeader>,
    write_ptr: Cell<*mut u8>,
    curr_free: Cell<usize>,

    default_capacity: Cell<usize>,
}

impl Arena {
    /// Constructs a new, empty arena.
    ///
    /// No memory is allocated, so this operation is very cheap.
    pub fn new() -> Arena {
        // Check that the ChunkHeader will be sufficiently aligned in our allocation,
        // and that the size of a ChunkHeader is an integer multiple of ALIGNMENT.
        // These checks will be optimized away in a release build.
        assert!(align_of::<ChunkHeader>() <= ALIGNMENT);
        assert_eq!(HEADER_SIZE % ALIGNMENT, 0);
        // Check that RawValue and MapEntry don't need larger alignment than we can provide.
        assert!(align_of::<RawValue>() <= ALIGNMENT);
        assert!(align_of::<MapEntry>() <= ALIGNMENT);

        Arena {
            curr_chunk: Cell::new(null_mut()),
            write_ptr: Cell::new(null_mut()),
            curr_free: Cell::new(0),
            default_capacity: Cell::new(4 * 1024 - HEADER_SIZE),
        }
    }

    /// Constructs a new arena with at least `cap` free bytes pre-allocated.
    pub fn with_capacity(cap: usize) -> Arena {
        let inst = Arena::new();
        if cap > 0 {
            inst.create_chunk(round_up(cap));
        }
        inst
    }

    /// Sets the minimum capacity of new memory chunks.
    ///
    /// # Panics
    ///
    /// Panics if `cap` is zero.
    pub fn set_default_capacity(&self, cap: usize) {
        assert!(cap > 0, "Arena default capacity cannot be zero");
        self.default_capacity.set(cap);
    }

    /// Resets the arena.
    ///
    /// All memory chunks are freed, except for the first one, which is marked as free.
    /// This is useful, for example, when slices are allocated and released in a loop.
    /// By calling `reset()` between iterations, the amortized number of memory allocations
    /// per iteration is effectively zero if the first chunk is large enough;
    /// see [`with_capacity`].
    ///
    /// [`with_capacity`]: Arena::with_capacity
    ///
    /// The compiler ensures that this method can only be called once there are
    /// no more live references to slices allocated in this arena.
    pub fn reset(&mut self) {
        let mut chunk = self.curr_chunk.get();
        if chunk.is_null() {
            debug_assert_eq!(self.curr_free.get(), 0);
            return;
        }
        loop {
            let header = unsafe { chunk.read() };
            if header.prev_chunk.is_null() {
                self.curr_chunk.set(chunk);
                self.write_ptr
                    .set((chunk as *mut u8).wrapping_add(HEADER_SIZE));
                self.curr_free.set(header.alloc_size - HEADER_SIZE);
                return;
            }
            chunk = unsafe { destroy_chunk(chunk) };
        }
    }

    /// Allocates and copies the given slice.
    pub fn bytes<'a>(&'a self, b: &[u8]) -> &'a mut [u8] {
        let ptr = self.alloc(b.len() * size_of::<u8>());
        unsafe {
            ptr.copy_from_nonoverlapping(b.as_ptr(), b.len());
            std::slice::from_raw_parts_mut(ptr, b.len())
        }
    }

    /// Allocates and copies the given string.
    pub fn string<'a>(&'a self, s: &str) -> &'a mut str {
        unsafe { from_utf8_unchecked_mut(self.bytes(s.as_bytes())) }
    }

    /// Allocates and copies the given slice.
    pub fn array<'a, 'b>(&'a self, items: &[RawValue<'b>]) -> &'a mut [RawValue<'b>] {
        let ptr = self.alloc(items.len() * size_of::<RawValue>()) as *mut RawValue;
        debug_assert_eq!(ptr as usize % align_of::<RawValue>(), 0);
        unsafe {
            ptr.copy_from_nonoverlapping(items.as_ptr(), items.len());
            std::slice::from_raw_parts_mut(ptr, items.len())
        }
    }

    /// Allocates and copies the given slice.
    pub fn map<'a, 'b>(&'a self, entries: &[MapEntry<'b>]) -> &'a mut [MapEntry<'b>] {
        let ptr = self.alloc(entries.len() * size_of::<MapEntry>()) as *mut MapEntry;
        debug_assert_eq!(ptr as usize % align_of::<MapEntry>(), 0);
        unsafe {
            ptr.copy_from_nonoverlapping(entries.as_ptr(), entries.len());
            std::slice::from_raw_parts_mut(ptr, entries.len())
        }
    }

    /// Reserves `size` bytes in the arena, aligned to `ALIGNMENT`,
    /// and returns a pointer to the memory area.
    fn alloc(&self, size: usize) -> *mut u8 {
        // Round up size to nearest multiple of ALIGNMENT
        let size = round_up(size);

        let curr_free = self.curr_free.get();
        if size > curr_free {
            self.create_chunk(std::cmp::max(size, self.default_capacity.get()));
        }
        debug_assert!(self.curr_free.get() >= size);
        let ptr = self.write_ptr.get();
        self.write_ptr.set(self.write_ptr.get().wrapping_add(size));
        self.curr_free.set(self.curr_free.get() - size);
        ptr
    }

    /// Allocates a new memory chunk with at least `cap` free bytes,
    /// initializes its header, and appends it to the chunk chain.
    fn create_chunk(&self, cap: usize) {
        assert!(cap <= usize::MAX - HEADER_SIZE);
        let alloc_size = cap + HEADER_SIZE;

        let layout = alloc::Layout::from_size_align(alloc_size, ALIGNMENT).unwrap();
        let (ptr, header_ptr);
        unsafe {
            // Safe because alloc_size is > 0
            ptr = alloc::alloc(layout);
            if ptr.is_null() {
                alloc::handle_alloc_error(layout);
            }
            header_ptr = ptr as *mut ChunkHeader;
            // Safe because ALIGNMENT is >= alignment of ChunkHeader
            // (checked in Arena::new())
            header_ptr.write(ChunkHeader {
                prev_chunk: self.curr_chunk.get(),
                alloc_size,
            });
        }

        self.curr_chunk.set(header_ptr);
        self.write_ptr.set(ptr.wrapping_add(HEADER_SIZE));
        self.curr_free.set(cap);
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        let mut chunk = self.curr_chunk.get();
        while !chunk.is_null() {
            chunk = unsafe { destroy_chunk(chunk) };
        }
    }
}

/// Rounds `n` up to be a multiple of `ALIGNMENT`.
fn round_up(n: usize) -> usize {
    (n + (ALIGNMENT - 1)) & !(ALIGNMENT - 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Map, Value};

    fn header_list(arena: &Arena) -> Vec<ChunkHeader> {
        let mut headers = vec![];
        let mut chunk_ptr = arena.curr_chunk.get();
        while !chunk_ptr.is_null() {
            let header = unsafe { chunk_ptr.read() };
            headers.push(header);
            chunk_ptr = header.prev_chunk;
        }
        headers.reverse();
        headers
    }

    #[test]
    fn arena_with_capacity() {
        let arena = Arena::with_capacity(33);
        let headers = header_list(&arena);
        assert_eq!(headers.len(), 1);
        assert!(arena.curr_free.get() >= 33);
        assert_eq!(headers[0].alloc_size, arena.curr_free.get() + HEADER_SIZE);
    }

    #[test]
    fn arena_bytes() {
        let arena = Arena::new();
        let x1 = &[];
        let x2 = &[17, 39, 1, 5];
        let x3 = &[5, 4, 3, 2, 1, 0];

        let y1 = arena.bytes(x1);
        let y2 = arena.bytes(x2);
        let y3 = arena.bytes(x3);

        // Check that allocated slices are equal to the originals,
        // but point to different memory areas.

        assert_eq!(y1, x1);
        assert_ne!(y1.as_ptr(), x1.as_ptr());

        assert_eq!(y2, x2);
        assert_ne!(y2.as_ptr(), x2.as_ptr());

        assert_eq!(y3, x3);
        assert_ne!(y3.as_ptr(), x3.as_ptr());
    }

    #[test]
    fn arena_string() {
        let arena = Arena::new();
        let x1 = "";
        let x2 = "zyx";
        let x3 = "abcdef";

        let y1 = arena.string(x1);
        let y2 = arena.string(x2);
        let y3 = arena.string(x3);

        // Check that allocated strings are equal to the originals,
        // but point to different memory areas.

        assert_eq!(y1, x1);
        assert_ne!(y1.as_ptr(), x1.as_ptr());

        assert_eq!(y2, x2);
        assert_ne!(y2.as_ptr(), x2.as_ptr());

        assert_eq!(y3, x3);
        assert_ne!(y3.as_ptr(), x3.as_ptr());
    }

    #[test]
    fn arena_array() {
        let arena = Arena::new();
        let x1 = &[];
        let x2 = &[
            Value::Int(5).into(),
            Value::String("123abc").into(),
            None.into(),
        ];
        let x3 = &[
            Value::Bytes(&[34, 19, 255]).into(),
            Value::Array(x1).into(),
            Value::Array(x2).into(),
        ];

        let y1 = arena.array(x1);
        let y2 = arena.array(x2);
        let y3 = arena.array(x3);

        // Check that allocated slices are equal to the originals,
        // but point to different memory areas.
        // Also check that the inner values point to the same memory areas
        // as the inner values of the originals.

        assert_eq!(y1, x1);
        assert_ne!(y1.as_ptr(), x1.as_ptr());

        assert_eq!(y2, x2);
        assert_ne!(y2.as_ptr(), x2.as_ptr());
        assert_eq!(
            y2[1].unpack().unwrap().string().unwrap().as_ptr(),
            x2[1].unpack().unwrap().string().unwrap().as_ptr(),
        );

        assert_eq!(y3, x3);
        assert_ne!(y3.as_ptr(), x3.as_ptr());
        assert_eq!(
            y3[0].unpack().unwrap().bytes().unwrap().as_ptr(),
            x3[0].unpack().unwrap().bytes().unwrap().as_ptr(),
        );
        assert_eq!(
            y3[1].unpack().unwrap().array().unwrap().as_ptr(),
            x3[1].unpack().unwrap().array().unwrap().as_ptr(),
        );
        assert_eq!(
            y3[2].unpack().unwrap().array().unwrap().as_ptr(),
            x3[2].unpack().unwrap().array().unwrap().as_ptr(),
        );
    }

    #[test]
    fn arena_map() {
        let arena = Arena::new();
        let x1: &[_] = &[];
        let x2: &[_] = &[
            MapEntry::new("asdf", Value::Int(-5)),
            MapEntry::new("key", Value::String("12345")),
            MapEntry::new("", Map::new(x1).into()),
        ];
        let m3 = &[MapEntry::new("k3", Value::Bytes(&[17, 27, 37]))];
        let x3: &[_] = &[
            MapEntry::new("k1", Map::new(x2).into()),
            MapEntry::new("k2", Map::new(m3).into()),
        ];

        let y1 = arena.map(x1);
        let y2 = arena.map(x2);
        let y3 = arena.map(x3);

        // Check that allocated slices are equal to the originals,
        // but point to different memory areas.
        // Also check that the inner values point to the same memory areas
        // as the inner values of the originals.

        assert_eq!(y1, x1);
        assert_ne!(y1.as_ptr(), x1.as_ptr());

        assert_eq!(y2, x2);
        assert_ne!(y2.as_ptr(), x2.as_ptr());
        assert_eq!(
            y2[1].value().string().unwrap().as_ptr(),
            x2[1].value().string().unwrap().as_ptr(),
        );
        assert_eq!(
            y2[2].value().map().unwrap().entries().as_ptr(),
            x2[2].value().map().unwrap().entries().as_ptr(),
        );

        assert_eq!(y3, x3);
        assert_ne!(y3.as_ptr(), x3.as_ptr());
        assert_eq!(
            y3[0].value().map().unwrap().entries().as_ptr(),
            x3[0].value().map().unwrap().entries().as_ptr(),
        );
        assert_eq!(
            y3[1].value().map().unwrap().entries().as_ptr(),
            x3[1].value().map().unwrap().entries().as_ptr(),
        );
    }

    #[test]
    fn arena_alloc() {
        let arena = Arena::new();
        assert!(header_list(&arena).is_empty());

        // Check that empty allocations don't create a new chunk
        let _ = arena.bytes(&[]);
        assert!(header_list(&arena).is_empty());

        // Check internal state after small allocation
        let x1 = &[128];
        let y1 = arena.bytes(x1);
        let headers = header_list(&arena);
        assert_eq!(headers.len(), 1);
        let chunk_size = headers[0].alloc_size;
        let num_free_1 = arena.curr_free.get();
        assert_eq!(chunk_size - HEADER_SIZE - ALIGNMENT, num_free_1,);

        // Allocate almost all of the remaining chunk
        let x2: Box<[u8]> = (0..(num_free_1 - ALIGNMENT - ALIGNMENT / 2))
            .map(|i| (i * 3) as u8)
            .collect();
        let y2 = arena.bytes(&x2);
        let headers = header_list(&arena);
        assert_eq!(headers.len(), 1);
        let num_free_2 = ALIGNMENT;
        assert_eq!(arena.curr_free.get(), num_free_2);

        // Allocate a little more memory than is left in chunk
        let x3: Box<[u8]> = (0..(ALIGNMENT + 1)).map(|i| (i * 5) as u8).collect();
        let y3 = arena.bytes(&x3);
        let headers = header_list(&arena);
        assert_eq!(headers.len(), 2);
        let num_free_3 = arena.default_capacity.get() - 2 * ALIGNMENT;
        assert_eq!(arena.curr_free.get(), num_free_3);

        // Allocate exactly as much memory as is left in chunk
        let x4: Box<[u8]> = (0..num_free_3).map(|i| (i * 7) as u8).collect();
        let y4 = arena.bytes(&x4);
        let headers = header_list(&arena);
        assert_eq!(headers.len(), 2);
        let num_free_4 = 0;
        assert_eq!(arena.curr_free.get(), num_free_4);

        // Allocate 1 byte to check that a new chunk is allocated
        let x5 = &[129];
        let y5 = arena.bytes(x5);
        let headers = header_list(&arena);
        assert_eq!(headers.len(), 3);
        let num_free_5 = arena.default_capacity.get() - ALIGNMENT;
        assert_eq!(arena.curr_free.get(), num_free_5);

        // Check that old  didn't get overwritten
        assert_eq!(y1, x1);
        assert_eq!(y2, &*x2);
        assert_eq!(y3, &*x3);
        assert_eq!(y4, &*x4);
        assert_eq!(y5, x5);
    }

    #[test]
    fn arena_reset() {
        let mut arena = Arena::new();

        // Allocate a single chunk, then reset the arena
        let _y1 = arena.bytes(&[1, 1, 2, 3, 5, 8, 13]);
        let curr_chunk_1 = arena.curr_chunk.get();
        let headers_1 = header_list(&arena);
        arena.reset();
        let headers_2 = header_list(&arena);
        assert_eq!(headers_2.len(), 1);
        assert_eq!(headers_2[0].prev_chunk, null_mut());
        assert_eq!(headers_1[0].alloc_size, headers_2[0].alloc_size);
        assert_eq!(arena.curr_chunk.get(), curr_chunk_1);
        assert_eq!(
            arena.write_ptr.get(),
            (curr_chunk_1 as *mut u8).wrapping_add(HEADER_SIZE),
        );
        assert_eq!(arena.curr_free.get(), headers_2[0].alloc_size - HEADER_SIZE);

        // Allocate several chunks, then reset the arena
        let x2: Box<[u8]> = (0..arena.default_capacity.get()).map(|i| i as u8).collect();
        let _y1 = arena.bytes(&x2);
        let _y2 = arena.bytes(&x2);
        let _y3 = arena.bytes(&x2);
        let headers_3 = header_list(&arena);
        assert_eq!(headers_3.len(), 3);
        arena.reset();
        let headers_4 = header_list(&arena);
        assert_eq!(headers_4.len(), 1);
        assert_eq!(headers_4[0].prev_chunk, null_mut());
        assert_eq!(headers_1[0].alloc_size, headers_4[0].alloc_size);
        assert_eq!(arena.curr_chunk.get(), curr_chunk_1);
        assert_eq!(
            arena.write_ptr.get(),
            (curr_chunk_1 as *mut u8).wrapping_add(HEADER_SIZE),
        );
        assert_eq!(arena.curr_free.get(), headers_4[0].alloc_size - HEADER_SIZE);
    }
}
