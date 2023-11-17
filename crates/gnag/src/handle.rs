use std::{
    error::Error,
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::{Index, IndexMut},
};

pub trait TypedHandle {
    fn new(index: usize) -> Self;
    fn index(self) -> usize;
}

#[macro_export]
macro_rules! simple_handle {
    ($($visibility:vis $name:ident),+) => {
        $(
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
            #[repr(transparent)]
            $visibility struct $name(u32);
            #[allow(unused)]
            impl $crate::handle::TypedHandle for $name {
                fn new(index: usize) -> Self {
                    assert!(index <= u32::MAX as usize);
                    Self(index as u32)
                }
                #[inline]
                fn index(self) -> usize {
                    self.0 as usize
                }
            }
        )+
    };
}
pub use simple_handle;

pub struct HandleCounter<H>(usize, PhantomData<H>);

impl<H: TypedHandle> HandleCounter<H> {
    pub fn new() -> Self {
        Self(0, PhantomData)
    }
    pub fn next(&mut self) -> H {
        let next = H::new(self.0);
        self.0 += 1;
        next
    }
    pub fn reset(&mut self) {
        self.0 = 0;
    }
}

pub struct HandleVec<H, T>(Vec<T>, PhantomData<H>);

impl<H, T> Default for HandleVec<H, T> {
    fn default() -> Self {
        Self(Vec::default(), PhantomData)
    }
}

impl<H, T: Clone> Clone for HandleVec<H, T> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotCompleteError;
impl Display for NotCompleteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NotCompleteError")
    }
}
impl Error for NotCompleteError {}

impl<H, T> TryFrom<SecondaryVec<H, T>> for HandleVec<H, T> {
    type Error = NotCompleteError;
    fn try_from(value: SecondaryVec<H, T>) -> Result<Self, Self::Error> {
        if let Some(vec) = value.0.into_iter().collect::<Option<Vec<_>>>() {
            Ok(HandleVec(vec, PhantomData))
        } else {
            Err(NotCompleteError)
        }
    }
}

impl<H: TypedHandle, T> HandleVec<H, T> {
    pub fn new() -> Self {
        HandleVec(Vec::new(), PhantomData)
    }
    pub fn map<A>(self, fun: impl FnMut(T) -> A) -> HandleVec<H, A> {
        HandleVec(self.into_iter().map(fun).collect(), PhantomData)
    }
    pub fn map_fill<A: Clone>(&self, value: A) -> HandleVec<H, A> {
        let vec = vec![value; self.len()];
        HandleVec(vec, PhantomData)
    }
    pub fn map_ref<A>(&self, fun: impl FnMut(&T) -> A) -> HandleVec<H, A> {
        HandleVec(self.iter().map(fun).collect(), PhantomData)
    }
    pub fn map_with_key<A>(self, mut fun: impl FnMut(H, T) -> A) -> HandleVec<H, A> {
        HandleVec(
            self.into_iter_kv().map(|(h, t)| fun(h, t)).collect(),
            PhantomData,
        )
    }
    pub fn map_ref_with_key<A>(&self, mut fun: impl FnMut(H, &T) -> A) -> HandleVec<H, A> {
        HandleVec(
            self.iter_kv().map(|(h, t)| fun(h, t)).collect(),
            PhantomData,
        )
    }
    pub fn with_capacity(capacity: usize) -> Self {
        HandleVec(Vec::with_capacity(capacity), PhantomData)
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn push(&mut self, value: T) -> H {
        let len = self.0.len();
        self.0.push(value);
        H::new(len)
    }
    pub fn get(&self, index: H) -> Option<&T> {
        self.0.get(index.index())
    }
    pub fn get_mut(&mut self, index: H) -> Option<&mut T> {
        self.0.get_mut(index.index())
    }
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.0.iter()
    }
    pub fn iter_kv(
        &self,
    ) -> impl Iterator<Item = (H, &T)> + Clone + ExactSizeIterator + DoubleEndedIterator {
        self.0.iter().enumerate().map(|(i, t)| (H::new(i), t))
    }
    pub fn into_iter_kv(
        self,
    ) -> impl Iterator<Item = (H, T)> + ExactSizeIterator + DoubleEndedIterator {
        self.0.into_iter().enumerate().map(|(i, t)| (H::new(i), t))
    }
    pub fn iter_keys(
        &self,
    ) -> impl Iterator<Item = H> + Clone + ExactSizeIterator + DoubleEndedIterator {
        (0..self.len()).map(H::new)
    }
    pub fn clear(&mut self) {
        self.0.clear()
    }
}

impl<H, T> Extend<T> for HandleVec<H, T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<H, T> FromIterator<T> for HandleVec<H, T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        HandleVec(Vec::from_iter(iter), PhantomData)
    }
}

impl<H: TypedHandle, T> Index<H> for HandleVec<H, T> {
    type Output = T;
    fn index(&self, index: H) -> &Self::Output {
        &self.0[index.index()]
    }
}

impl<H: TypedHandle, T> IndexMut<H> for HandleVec<H, T> {
    fn index_mut(&mut self, index: H) -> &mut Self::Output {
        &mut self.0[index.index()]
    }
}

impl<H, T: Debug> Debug for HandleVec<H, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl<H, T> IntoIterator for HandleVec<H, T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, H, T> IntoIterator for &'a HandleVec<H, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

pub struct SecondaryVec<H, T>(Vec<Option<T>>, PhantomData<H>);

impl<H, T> Default for SecondaryVec<H, T> {
    fn default() -> Self {
        Self(Vec::default(), PhantomData)
    }
}

impl<H: TypedHandle, T> SecondaryVec<H, T> {
    pub fn new() -> Self {
        SecondaryVec(Vec::new(), PhantomData)
    }
    pub fn new_preallocated<T_>(primary: &HandleVec<H, T_>) -> Self {
        let n_none = (0..primary.len()).map(|_| None);
        SecondaryVec(n_none.collect(), PhantomData)
    }
    pub fn map<A>(self, mut fun: impl FnMut(T) -> A) -> SecondaryVec<H, A> {
        SecondaryVec(
            self.0
                .into_iter()
                .map(|option| match option {
                    Some(some) => Some(fun(some)),
                    None => None,
                })
                .collect(),
            PhantomData,
        )
    }
    pub fn map_ref<A>(&self, mut fun: impl FnMut(&T) -> A) -> SecondaryVec<H, A> {
        SecondaryVec(
            self.0
                .iter()
                .map(|option| match option {
                    Some(some) => Some(fun(some)),
                    None => None,
                })
                .collect(),
            PhantomData,
        )
    }
    pub fn with_capacity(capacity: usize) -> Self {
        SecondaryVec(Vec::with_capacity(capacity), PhantomData)
    }
    pub fn insert(&mut self, at: H, value: T) -> Option<T> {
        let index = at.index();
        if index >= self.0.len() {
            let add = self.0.len()..=index;
            self.0.extend(add.map(|_| None));
        }

        let old = std::mem::replace(&mut self.0[index], Some(value));
        return old;
    }
    pub fn contains(&self, index: H) -> bool {
        self.0.get(index.index()).is_some()
    }
    pub fn get(&self, index: H) -> Option<&T> {
        let get = self.0.get(index.index());
        match get {
            Some(some) => some.as_ref(),
            None => None,
        }
    }
    pub fn get_mut(&mut self, index: H) -> Option<&mut T> {
        let get = self.0.get_mut(index.index());
        match get {
            Some(some) => some.as_mut(),
            None => None,
        }
    }
    pub fn entry(&mut self, index: H) -> &mut Option<T> {
        let index = index.index();
        if index >= self.0.len() {
            let add = self.0.len()..=index;
            self.0.extend(add.map(|_| None));
        }

        &mut self.0[index]
    }
    pub fn iter(&self) -> std::iter::Flatten<std::slice::Iter<'_, Option<T>>> {
        self.0.iter().flatten()
    }
    pub fn iter_mut(&mut self) -> std::iter::Flatten<std::slice::IterMut<'_, Option<T>>> {
        self.0.iter_mut().flatten()
    }
    pub fn iter_kv(&self) -> impl Iterator<Item = (H, &T)> + Clone + DoubleEndedIterator {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, t)| t.as_ref().map(|t| (H::new(i), t)))
    }
    pub fn iter_kv_mut(&mut self) -> impl Iterator<Item = (H, &mut T)> + DoubleEndedIterator {
        self.0
            .iter_mut()
            .enumerate()
            .filter_map(|(i, t)| t.as_mut().map(|t| (H::new(i), t)))
    }
    pub fn iter_keys(&self) -> impl Iterator<Item = H> + Clone + DoubleEndedIterator + '_ {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, t)| t.is_some().then_some(H::new(i)))
    }
}

impl<H: TypedHandle, T> Index<H> for SecondaryVec<H, T> {
    type Output = T;
    fn index(&self, index: H) -> &Self::Output {
        self.0[index.index()].as_ref().unwrap()
    }
}

impl<H: TypedHandle, T> IndexMut<H> for SecondaryVec<H, T> {
    fn index_mut(&mut self, index: H) -> &mut Self::Output {
        self.0[index.index()].as_mut().unwrap()
    }
}

impl<H: TypedHandle + Debug, T: Debug> Debug for SecondaryVec<H, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter_kv()).finish()
    }
}

impl<H, T> IntoIterator for SecondaryVec<H, T> {
    type Item = T;
    type IntoIter = std::iter::Flatten<std::vec::IntoIter<Option<T>>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().flatten()
    }
}

impl<'a, H, T> IntoIterator for &'a SecondaryVec<H, T> {
    type Item = &'a T;
    type IntoIter = std::iter::Flatten<std::slice::Iter<'a, Option<T>>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().flatten()
    }
}

impl<H: TypedHandle, T> Extend<(H, T)> for SecondaryVec<H, T> {
    fn extend<I: IntoIterator<Item = (H, T)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<H: TypedHandle, T> FromIterator<(H, T)> for SecondaryVec<H, T> {
    fn from_iter<I: IntoIterator<Item = (H, T)>>(iter: I) -> Self {
        let mut vec = SecondaryVec::new();
        vec.extend(iter);
        vec
    }
}

pub struct HandleBitset<H> {
    set: Vec<usize>,
    spooky: PhantomData<H>,
}

impl<H> Clone for HandleBitset<H> {
    fn clone(&self) -> Self {
        Self {
            set: self.set.clone(),
            spooky: PhantomData,
        }
    }
}

impl<H: TypedHandle> HandleBitset<H> {
    pub fn new() -> HandleBitset<H> {
        Self {
            set: Vec::new(),
            spooky: PhantomData,
        }
    }
    pub fn replace(&mut self, handle: H, value: bool) -> bool {
        replace_impl(&mut self.set, handle.index(), value)
    }
    pub fn set(&mut self, handle: H, value: bool) {
        replace_impl(&mut self.set, handle.index(), value);
    }
    pub fn insert(&mut self, handle: H) -> bool {
        replace_impl(&mut self.set, handle.index(), true)
    }
    pub fn remove(&mut self, handle: H) -> bool {
        let index = handle.index();
        let word = index / std::mem::size_of::<usize>();

        if word >= self.set.len() {
            return false;
        }

        replace_impl(&mut self.set, index, false)
    }
}

fn replace_impl(storage: &mut Vec<usize>, index: usize, value: bool) -> bool {
    let word = index / std::mem::size_of::<usize>();
    let bit = index % std::mem::size_of::<usize>();

    if word >= storage.len() {
        storage.resize(word + 1, 0);
    }

    let new = (value as usize) << bit;
    let one = 1 << bit;
    let mask = !one;

    let prev = (storage[word] & one) == one;
    storage[word] = new | (storage[word] & mask);
    prev
}
