use std::collections::HashMap;

use gnag_runtime::trace::{PreorderTrace, Tokens};

use crate::handle::ItemHandle;

type ItemVec<T> = Vec<T>;

pub struct File {
    tokens: Tokens,
    parsed: PreorderTrace,

    name_to_item: HashMap<String, ItemHandle>,
    items: (),

    item: ItemVec<()>,
}
