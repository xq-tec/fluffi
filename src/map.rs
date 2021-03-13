// Copyright (C) 2021 xq-Tec GmbH

use std::fmt;

use crate::{RawString, RawValue, Value};

#[derive(Copy, Clone)]
pub struct Map<'a, 'b> {
    entries: &'b [MapEntry<'a>],
}

impl<'a, 'b> Map<'a, 'b> {
    pub const fn new(entries: &'b [MapEntry<'a>]) -> Map<'a, 'b> {
        Map { entries }
    }

    pub const fn entries(self) -> &'b [MapEntry<'a>] {
        self.entries
    }

    pub const fn len(self) -> usize {
        self.entries.len()
    }

    pub fn lookup(self, key: &str) -> Option<Value<'a>> {
        self.entries
            .iter()
            .find(|entry| entry.key() == key)
            .map(|entry| entry.value())
    }
}

impl<'a, 'b> fmt::Debug for Map<'a, 'b> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map()
            .entries(
                self.entries
                    .iter()
                    .map(|entry| (entry.key(), entry.value())),
            )
            .finish()
    }
}

macro_rules! map_from_array_impl {
    ($n:expr) => {
        impl<'a, 'b> From<&'b [MapEntry<'a>; $n]> for Map<'a, 'b> {
            fn from(entries: &'b [MapEntry<'a>; $n]) -> Map<'a, 'b> {
                Map { entries }
            }
        }
    };
}

map_from_array_impl!(0);
map_from_array_impl!(1);
map_from_array_impl!(2);
map_from_array_impl!(3);
map_from_array_impl!(4);
map_from_array_impl!(5);
map_from_array_impl!(6);
map_from_array_impl!(7);
map_from_array_impl!(8);

impl<'a, 'b> From<&'b [MapEntry<'a>]> for Map<'a, 'b> {
    fn from(entries: &'b [MapEntry<'a>]) -> Map<'a, 'b> {
        Map { entries }
    }
}

impl<'a, 'b> IntoIterator for Map<'a, 'b> {
    type IntoIter = MapIterator<'a, 'b>;

    type Item = <MapIterator<'a, 'b> as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        MapIterator {
            inner: self.entries.into_iter(),
        }
    }
}

pub struct MapIterator<'a, 'b> {
    inner: std::slice::Iter<'b, MapEntry<'a>>,
}

impl<'a, 'b> Iterator for MapIterator<'a, 'b> {
    type Item = (&'a str, Value<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|entry| (entry.key(), entry.value()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, 'b> ExactSizeIterator for MapIterator<'a, 'b> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, 'b> DoubleEndedIterator for MapIterator<'a, 'b> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|entry| (entry.key(), entry.value()))
    }
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct MapEntry<'a> {
    key: RawString<'a>,
    value: RawValue<'a>,
}

impl<'a> MapEntry<'a> {
    pub const fn new(key: &'a str, value: Value<'a>) -> MapEntry<'a> {
        MapEntry {
            key: RawString::new(key),
            value: RawValue::new_non_null(value),
        }
    }

    pub fn from_raw(key: RawString<'a>, value: RawValue<'a>) -> MapEntry<'a> {
        assert!(!value.is_null());
        MapEntry { key, value }
    }

    pub fn key(&self) -> &'a str {
        self.key.into()
    }

    pub fn value(&self) -> Value<'a> {
        self.value
            .unpack()
            .expect("value in MapEntry must not be NULL")
    }

    pub const fn raw_key(&self) -> RawString<'a> {
        self.key
    }

    pub const fn raw_value(&self) -> RawValue<'a> {
        self.value
    }
}

impl<'a> fmt::Debug for MapEntry<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.key.fmt(f)?;
        f.write_str(": ")?;
        self.value.fmt(f)?;
        Ok(())
    }
}
