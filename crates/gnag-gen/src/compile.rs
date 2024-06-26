use gnag::{ctx::ErrorAccumulator, handle::HandleVec};

use crate::{
    convert::{RuleHandle, TokenHandle},
    graph::{GraphBuilder, NodeHandle, PegNode, TokenOrRule},
    lower::LoweredFile,
};

pub struct CompiledGraph {
    pub entry: NodeHandle,
    pub nodes: HandleVec<NodeHandle, PegNode>,
}

pub struct CompiledFile {
    pub tokens: HandleVec<TokenHandle, CompiledGraph>,
    pub rules: HandleVec<RuleHandle, CompiledGraph>,
}

impl CompiledFile {
    pub fn new(err: &ErrorAccumulator, file: &LoweredFile, optimize: bool) -> CompiledFile {
        let mut builder = GraphBuilder::new(err);

        let tokens = file.tokens.map_ref_with_key(|handle, expr| {
            let entry = builder.convert_rule(TokenOrRule::Token(handle), expr, optimize);
            let nodes = builder.finish();
            CompiledGraph { entry, nodes }
        });

        let rules = file.rules.map_ref_with_key(|handle, expr| {
            let entry = builder.convert_rule(TokenOrRule::Rule(handle), expr, optimize);
            let nodes = builder.finish();
            CompiledGraph { entry, nodes }
        });

        CompiledFile { tokens, rules }
    }
}
