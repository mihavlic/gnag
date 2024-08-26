#[derive(Clone)]
pub struct ResetableSlice<'a, T> {
    iter: std::slice::Iter<'a, T>,
    slice: &'a [T],
}

impl<'a, T> ResetableSlice<'a, T> {
    pub fn new(slice: &'a [T]) -> Self {
        Self {
            iter: slice.iter(),
            slice,
        }
    }
    pub fn get_position(&self) -> usize {
        let total = self.slice.len();
        let less = self.iter.as_slice().len();
        total - less
    }
    pub fn set_position(&mut self, position: usize) {
        self.iter = self.slice[position..].iter();
    }
    pub fn remaining(&self) -> &'a [T] {
        self.iter.as_slice()
    }
    pub fn inner_slice(&self) -> &'a [T] {
        self.slice
    }
    pub fn is_empty(&self) -> bool {
        self.iter.len() == 0
    }
    pub fn len(&self) -> usize {
        self.iter.len()
    }
    pub fn skip(&mut self, count: usize) {
        // TODO use Iterator::advance_by when it's stable
        let slice = self.iter.as_slice();
        let skip = usize::min(slice.len(), count);
        self.iter = slice[skip..].iter();
    }
    pub fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }
    pub fn peek(&self) -> Option<&'a T> {
        self.iter.clone().next()
    }
}

impl<'a, T> IntoIterator for ResetableSlice<'a, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}
