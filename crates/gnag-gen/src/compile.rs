use gnag::{ctx::ErrorAccumulator, handle::HandleVec};

use crate::{
    convert::{ConvertedFile, RuleHandle},
    graph::{GraphBuilder, NodeHandle, PegNode},
    lower::LoweredFile,
};

pub struct CompiledGraph {
    pub entry: NodeHandle,
    pub nodes: HandleVec<NodeHandle, PegNode>,
}

pub struct CompiledFile {
    pub rules: HandleVec<RuleHandle, CompiledGraph>,
}

impl CompiledFile {
    pub fn new(
        err: &ErrorAccumulator,
        converted: &ConvertedFile,
        file: &LoweredFile,
        optimize: bool,
    ) -> CompiledFile {
        let mut builder = GraphBuilder::new(err);

        let rules = file.rules.map_ref_with_key(|handle, expr| {
            let converted = &converted.rules[handle];
            let entry = builder.convert_rule(handle, converted.kind, expr, optimize);
            let nodes = builder.finish();
            CompiledGraph { entry, nodes }
        });

        CompiledFile { rules }
    }
}
