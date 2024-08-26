use std::{fmt::Debug, num::NonZeroU32};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ItemKind {
    Token = 0,
    Rule = 1,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemHandle(NonZeroU32);
impl ItemHandle {
    pub fn from_raw(kind: ItemKind, index: u32) -> ItemHandle {
        assert!(index < (1 << 30), "Index is too large");

        let tag = match kind {
            ItemKind::Token => 0,
            ItemKind::Rule => 1,
        };

        // <30 bits index> <1 bit always 1> <1 bit tag>
        let raw = (index << 2) | 0b10 | tag;
        Self(NonZeroU32::new(raw).unwrap())
    }
    pub fn get_kind(self) -> ItemKind {
        let raw = self.0.get();
        let tag = raw & 0b1;

        match tag {
            0 => ItemKind::Token,
            1 => ItemKind::Rule,
            _ => unreachable!(),
        }
    }
    pub fn get_index(self) -> u32 {
        let raw = self.0.get();
        raw >> 2
    }
    pub fn into_raw(self) -> (ItemKind, u32) {
        let kind = self.get_kind();
        let index = self.get_index();
        (kind, index)
    }
    pub fn try_into_token(self) -> Option<TokenHandle> {
        let (kind, _) = self.into_raw();
        if kind == ItemKind::Token {
            return Some(TokenHandle(self.0));
        } else {
            return None;
        }
    }
    pub fn try_into_rule(self) -> Option<RuleHandle> {
        let (kind, _) = self.into_raw();
        if kind == ItemKind::Rule {
            return Some(RuleHandle(self.0));
        } else {
            return None;
        }
    }
}

impl Debug for ItemHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ItemHandle")
            .field(&self.get_kind())
            .field(&self.get_index())
            .finish()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TokenHandle(NonZeroU32);
impl TokenHandle {
    pub fn into_item(self) -> ItemHandle {
        ItemHandle(self.0)
    }
    pub fn get_index(self) -> u32 {
        let raw = self.0.get();
        raw >> 2
    }
}

impl Debug for TokenHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("TokenHandle")
            .field(&self.get_index())
            .finish()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct RuleHandle(NonZeroU32);
impl RuleHandle {
    pub fn into_item(self) -> ItemHandle {
        ItemHandle(self.0)
    }
    pub fn get_index(self) -> u32 {
        let raw = self.0.get();
        raw >> 2
    }
}

impl Debug for RuleHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("RuleHandle")
            .field(&self.get_index())
            .finish()
    }
}

pub struct Database {}
