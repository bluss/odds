use std::ops;

pub trait CheckedIndex<Idx>: ops::Index<Idx> {
    fn checked_index(&self, index: Idx) -> Option<&Self::Output> {
        if self.has_index(&index) {
            Some(&self[index])
        } else {
            None
        }
    }
    fn has_index(&self, index: &Idx) -> bool;
}

pub trait CheckedIndexMut<Idx>: ops::IndexMut<Idx>+CheckedIndex<Idx> {
    fn checked_index_mut(&mut self, index: Idx) -> Option<&mut Self::Output> {
        if self.has_index(&index) {
            Some(&mut self[index])
        } else {
            None
        }
    }
}

impl<T> CheckedIndex<usize> for [T] {
    fn has_index(&self, &index: &usize) -> bool {
        index < self.len()
    }
}

impl<T> CheckedIndex<ops::RangeFrom<usize>> for [T] {
    fn has_index(&self, index: &ops::RangeFrom<usize>) -> bool {
        self.has_index(&(index.start..self.len()))
    }
}

impl<T> CheckedIndex<ops::RangeTo<usize>> for [T] {
    fn has_index(&self, index: &ops::RangeTo<usize>) -> bool {
        self.has_index(&(0..index.end))
    }
}

impl<T> CheckedIndex<ops::Range<usize>> for [T] {
    fn has_index(&self, index: &ops::Range<usize>) -> bool {
        assert!(index.start <= index.end);
        index.end <= self.len()
    }
}

impl<I,T> CheckedIndexMut<I> for [T] where [T]: ops::IndexMut<I>+CheckedIndex<I> { }
