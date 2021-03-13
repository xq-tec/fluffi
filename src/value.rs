// Copyright (C) 2021 xq-Tec GmbH

use std::fmt;

use crate::map::{Map, MapEntry};
use crate::raw::RawValue;

#[derive(Copy, Clone)]
pub enum Value<'a> {
    Bool(bool),
    Int(i64),
    Float(f64),
    Blob(&'a [u8]),
    String(&'a str),
    Array(&'a [RawValue<'a>]),
    Map(Map<'a, 'a>),
}

impl<'a> Value<'a> {
    pub const fn is_bool(self) -> bool {
        matches!(self, Value::Bool(_))
    }

    pub const fn bool(self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(b),
            _ => None,
        }
    }

    pub const fn is_number(self) -> bool {
        matches!(self, Value::Int(_) | Value::Float(_))
    }

    pub const fn is_int(self) -> bool {
        matches!(self, Value::Int(_))
    }

    pub const fn int(self) -> Option<i64> {
        match self {
            Value::Int(i) => Some(i),
            _ => None,
        }
    }

    pub const fn is_float(self) -> bool {
        matches!(self, Value::Float(_))
    }

    pub const fn float(self) -> Option<f64> {
        match self {
            Value::Int(i) => Some(i as f64),
            Value::Float(f) => Some(f),
            _ => None,
        }
    }

    pub const fn is_blob(self) -> bool {
        matches!(self, Value::Blob(_))
    }

    pub const fn blob(self) -> Option<&'a [u8]> {
        match self {
            Value::Blob(b) => Some(b),
            Value::String(s) => Some(s.as_bytes()),
            _ => None,
        }
    }

    pub const fn is_string(self) -> bool {
        matches!(self, Value::String(_))
    }

    pub const fn string(self) -> Option<&'a str> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    pub const fn is_array(self) -> bool {
        matches!(self, Value::Array(_))
    }

    pub const fn array(self) -> Option<&'a [RawValue<'a>]> {
        match self {
            Value::Array(a) => Some(a),
            _ => None,
        }
    }

    pub const fn is_map(self) -> bool {
        matches!(self, Value::Map(_))
    }

    pub const fn map(self) -> Option<Map<'a, 'a>> {
        match self {
            Value::Map(m) => Some(m),
            _ => None,
        }
    }
}

impl<'a> From<bool> for Value<'a> {
    fn from(b: bool) -> Value<'static> {
        Value::Bool(b)
    }
}

macro_rules! value_from_int_impl {
    ($t:ty) => {
        impl<'a> From<$t> for Value<'a> {
            fn from(v: $t) -> Value<'static> {
                Value::Int(v as i64)
            }
        }
    };
}

value_from_int_impl!(u8);
value_from_int_impl!(u16);
value_from_int_impl!(u32);
value_from_int_impl!(i8);
value_from_int_impl!(i16);
value_from_int_impl!(i32);
value_from_int_impl!(i64);

impl<'a> From<f32> for Value<'a> {
    fn from(v: f32) -> Value<'static> {
        Value::Float(v as f64)
    }
}

impl<'a> From<f64> for Value<'a> {
    fn from(v: f64) -> Value<'static> {
        Value::Float(v)
    }
}

impl<'a> From<&'a [u8]> for Value<'a> {
    fn from(b: &'a [u8]) -> Value<'a> {
        Value::Blob(b)
    }
}

impl<'a> From<&'a str> for Value<'a> {
    fn from(s: &'a str) -> Value<'a> {
        Value::String(s)
    }
}

macro_rules! value_from_array_impl {
    ($n:expr) => {
        impl<'a> From<&'a [RawValue<'a>; $n]> for Value<'a> {
            fn from(v: &'a [RawValue<'a>; $n]) -> Value<'a> {
                Value::Array(v)
            }
        }
    };
}

value_from_array_impl!(0);
value_from_array_impl!(1);
value_from_array_impl!(2);
value_from_array_impl!(3);
value_from_array_impl!(4);
value_from_array_impl!(5);
value_from_array_impl!(6);
value_from_array_impl!(7);
value_from_array_impl!(8);

impl<'a> From<&'a [RawValue<'a>]> for Value<'a> {
    fn from(v: &'a [RawValue<'a>]) -> Value<'a> {
        Value::Array(v)
    }
}

macro_rules! value_from_map_entry_array_impl {
    ($n:expr) => {
        impl<'a> From<&'a [MapEntry<'a>; $n]> for Value<'a> {
            fn from(v: &'a [MapEntry<'a>; $n]) -> Value<'a> {
                Value::Map(Map::new(v))
            }
        }
    };
}

value_from_map_entry_array_impl!(0);
value_from_map_entry_array_impl!(1);
value_from_map_entry_array_impl!(2);
value_from_map_entry_array_impl!(3);
value_from_map_entry_array_impl!(4);
value_from_map_entry_array_impl!(5);
value_from_map_entry_array_impl!(6);
value_from_map_entry_array_impl!(7);
value_from_map_entry_array_impl!(8);

impl<'a> From<&'a [MapEntry<'a>]> for Value<'a> {
    fn from(v: &'a [MapEntry<'a>]) -> Value<'a> {
        Value::Map(Map::new(v))
    }
}

impl<'a> From<Map<'a, 'a>> for Value<'a> {
    fn from(m: Map<'a, 'a>) -> Value<'a> {
        Value::Map(m)
    }
}

impl<'a, T: Into<Value<'a>>> From<&'a T> for Value<'a> {
    fn from(v: &'a T) -> Value<'a> {
        v.into()
    }
}

impl<'a> From<RawValue<'a>> for Option<Value<'a>> {
    fn from(v: RawValue<'a>) -> Option<Value<'a>> {
        v.unpack()
    }
}

impl<'a> From<Option<Value<'a>>> for RawValue<'a> {
    fn from(v: Option<Value<'a>>) -> RawValue<'a> {
        RawValue::new(v)
    }
}

impl<'a> From<Value<'a>> for RawValue<'a> {
    fn from(v: Value<'a>) -> RawValue<'a> {
        RawValue::new_non_null(v)
    }
}

impl<'a> fmt::Debug for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Value::*;
        match self {
            Bool(v) => f.write_str(if *v { "true" } else { "false" }),
            Int(v) => f.write_fmt(format_args!("{}", v)),
            Float(v) => f.write_fmt(format_args!("{}", v)),
            Blob(v) => f.write_fmt(format_args!("{:02x?}", v)),
            String(v) => f.write_fmt(format_args!("{}", v)),
            Array(v) => f.debug_list().entries(v.iter()).finish(),
            Map(v) => v.fmt(f),
        }
    }
}
