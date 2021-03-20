// Copyright (C) 2021 xq-Tec GmbH

use std::cmp;
use std::fmt;

use crate::{Map, MapEntry, Value};

pub const MAX_LENGTH: u64 = (1 << (64 - 16)) - 1;

#[derive(Copy, Clone)]
#[repr(u8)]
enum RawValueKind {
    Null = 0,
    Bool = 1,
    Int = 2,
    Float = 3,
    Bytes = 4,
    String = 5,
    Array = 6,
    Map = 7,
}

#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
struct Metadata(u64);

impl Metadata {
    const fn new(kind: RawValueKind) -> Metadata {
        Metadata(kind as u64)
    }

    const fn with_len(kind: RawValueKind, len: usize) -> Metadata {
        Metadata(kind as u64 | ((len as u64) << 16))
    }

    fn kind(&self) -> RawValueKind {
        unsafe { std::mem::transmute(self.0 as u8) }
    }

    fn len(&self) -> usize {
        debug_assert!(self.0 >> 16 < usize::MAX as u64);
        (self.0 >> 16) as usize
    }
}

#[derive(Copy, Clone)]
#[repr(C)]
union RawValuePayload<'a> {
    bool_v: bool,
    int_v: i64,
    float_v: f64,
    bytes: *const u8,
    items: *const RawValue<'a>,
    entries: *const MapEntry<'a>,
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct RawValue<'a> {
    md: Metadata,
    payload: RawValuePayload<'a>,
}

impl<'a> RawValue<'a> {
    pub const NULL: RawValue<'static> = RawValue {
        md: Metadata::new(RawValueKind::Null),
        payload: RawValuePayload { int_v: 0 },
    };

    pub const fn new(v: Option<Value<'a>>) -> RawValue<'a> {
        if let Some(v) = v {
            Self::new_non_null(v)
        } else {
            Self::NULL
        }
    }

    pub const fn new_non_null(v: Value<'a>) -> RawValue<'a> {
        use Value::*;
        match v {
            Bool(bool_v) => RawValue {
                md: Metadata::new(RawValueKind::Bool),
                payload: RawValuePayload { bool_v },
            },
            Int(int_v) => RawValue {
                md: Metadata::new(RawValueKind::Int),
                payload: RawValuePayload { int_v },
            },
            Float(float_v) => RawValue {
                md: Metadata::new(RawValueKind::Float),
                payload: RawValuePayload { float_v },
            },
            Bytes(b) => RawValue {
                md: Metadata::with_len(RawValueKind::Bytes, b.len()),
                payload: RawValuePayload { bytes: b.as_ptr() },
            },
            String(s) => RawValue {
                md: Metadata::with_len(RawValueKind::String, s.len()),
                payload: RawValuePayload { bytes: s.as_ptr() },
            },
            Array(a) => RawValue {
                md: Metadata::with_len(RawValueKind::Array, a.len()),
                payload: RawValuePayload { items: a.as_ptr() },
            },
            Map(m) => RawValue {
                md: Metadata::with_len(RawValueKind::Map, m.len()),
                payload: RawValuePayload {
                    entries: m.entries().as_ptr(),
                },
            },
        }
    }

    pub fn unpack(self) -> Option<Value<'a>> {
        match self.md.kind() {
            RawValueKind::Null => None,
            RawValueKind::Bool => Some(Value::Bool(unsafe { self.payload.bool_v })),
            RawValueKind::Int => Some(Value::Int(unsafe { self.payload.int_v })),
            RawValueKind::Float => Some(Value::Float(unsafe { self.payload.float_v })),
            RawValueKind::Bytes => unsafe {
                let len = self.md.len();
                Some(Value::Bytes(std::slice::from_raw_parts(
                    self.payload.bytes,
                    len,
                )))
            },
            RawValueKind::String => unsafe {
                let len = self.md.len();
                let bytes = std::slice::from_raw_parts(self.payload.bytes, len);
                debug_assert!(
                    std::str::from_utf8(bytes).is_ok(),
                    "string isn't a valid UTF-8 sequence",
                );
                Some(Value::String(std::str::from_utf8_unchecked(bytes)))
            },
            RawValueKind::Array => unsafe {
                let len = self.md.len();
                let items = std::slice::from_raw_parts(self.payload.items, len);
                Some(Value::Array(items))
            },
            RawValueKind::Map => unsafe {
                let len = self.md.len();
                let entries = std::slice::from_raw_parts(self.payload.entries, len);
                Some(Value::Map(Map::new(entries)))
            },
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self.md.kind(), RawValueKind::Null)
    }
}

unsafe impl<'a> Send for RawValue<'a> {}
unsafe impl<'a> Sync for RawValue<'a> {}

impl<'a> fmt::Debug for RawValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.unpack().fmt(f)
    }
}

impl<'a, 'b> cmp::PartialEq<RawValue<'b>> for RawValue<'a> {
    fn eq(&self, other: &RawValue) -> bool {
        if self.md != other.md {
            false
        } else {
            self.unpack() == other.unpack()
        }
    }
}
