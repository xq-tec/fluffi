// Copyright (C) 2021 xq-Tec GmbH

use std::cmp;
use std::fmt;
use std::hash;
use std::marker::PhantomData;
use std::ptr::NonNull;

/// FFI-safe wrapper around `&str`.
///
/// Rust code should generally interact with this type by `deref()`ing it to `&str`.
#[derive(Copy, Clone)]
#[repr(C)]
pub struct RawString<'a> {
    /// Pointer to a UTF8-encoded string. Note that the string is *not* null-terminated.
    ///
    /// FFI: This pointer must be non-NULL, even if `len` is zero. This constraint
    /// allows encoding an invalid/uninitialized state by setting `chars` to NULL
    /// (which corresponds to a `None` value of type `Option<RawString>`).
    chars: NonNull<u8>,
    /// The length of the string in bytes.
    len: usize,
    _marker: PhantomData<&'a str>,
}

impl<'a> RawString<'a> {
    pub const fn new(s: &'a str) -> RawString<'a> {
        RawString {
            chars: unsafe { NonNull::new_unchecked(s.as_ptr() as *mut u8) },
            len: s.len(),
            _marker: PhantomData,
        }
    }
}

impl<'a> cmp::PartialEq for RawString<'a> {
    fn eq(&self, other: &RawString) -> bool {
        let s1: &str = self.into();
        let s2: &str = other.into();
        s1 == s2
    }
}

impl<'a> cmp::Eq for RawString<'a> {}

impl<'a> cmp::PartialEq<&str> for RawString<'a> {
    fn eq(&self, other: &&str) -> bool {
        let s: &str = self.into();
        s == *other
    }
}

impl<'a> cmp::PartialEq<RawString<'a>> for str {
    fn eq(&self, other: &RawString) -> bool {
        let s: &str = other.into();
        self == s
    }
}

impl<'a> cmp::PartialOrd for RawString<'a> {
    fn partial_cmp(&self, other: &RawString) -> Option<cmp::Ordering> {
        let s1: &str = self.into();
        let s2: &str = other.into();
        s1.partial_cmp(s2)
    }
}

impl<'a> cmp::Ord for RawString<'a> {
    fn cmp(&self, other: &RawString) -> cmp::Ordering {
        let s1: &str = self.into();
        let s2: &str = other.into();
        s1.cmp(s2)
    }
}

impl<'a> hash::Hash for RawString<'a> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        let s: &str = self.into();
        s.hash(state);
    }
}

impl<'a> fmt::Display for RawString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s: &str = self.into();
        s.fmt(f)
    }
}

impl<'a> fmt::Debug for RawString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s: &str = self.into();
        s.fmt(f)
    }
}

impl<'a> From<&'a str> for RawString<'a> {
    fn from(s: &'a str) -> RawString<'a> {
        RawString::new(s)
    }
}

impl<'a> From<RawString<'a>> for &'a str {
    fn from(s: RawString<'a>) -> &'a str {
        unsafe {
            let bytes: &'a [u8] = std::slice::from_raw_parts(s.chars.as_ptr(), s.len);
            std::str::from_utf8_unchecked(bytes)
        }
    }
}

impl<'a> From<&RawString<'a>> for &'a str {
    fn from(s: &RawString<'a>) -> &'a str {
        (*s).into()
    }
}

unsafe impl<'a> Send for RawString<'a> {}
unsafe impl<'a> Sync for RawString<'a> {}
