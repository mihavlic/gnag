use std::collections::HashSet;

use gnag::{
    ctx::ErrorAccumulator,
    handle::{HandleBitset, HandleVec, SecondaryVec},
};

use crate::{
    convert::{ConvertedFile, RuleHandle},
    expr::Transition,
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

        let mut hashset = HashSet::new();
        let prefix_rules = rules.map_ref(|graph| find_prefix_rules(graph, &mut hashset));

        let mut left_recursions = SecondaryVec::new();
        let mut visited = HandleBitset::with_capacity(rules.len());
        let mut stack = Vec::new();

        for handle in rules.iter_keys() {
            find_prefix_cycles(
                handle,
                &prefix_rules,
                &mut left_recursions,
                &mut visited,
                &mut stack,
            );
            assert!(stack.is_empty());
        }

        for (handle, through) in left_recursions.iter_kv_mut() {
            let span = converted.rules[handle].body.name_span;
            for &mut child in through {
                let name = child.name(converted);
                err.error(
                    span,
                    format_args!("Rule is left-recursive through {}", name),
                );
            }
        }

        CompiledFile { rules }
    }
}

fn find_prefix_rules(graph: &CompiledGraph, set: &mut HashSet<RuleHandle>) -> Vec<RuleHandle> {
    set.clear();
    GraphBuilder::visit_edges_once_dfs(
        &graph.nodes,
        graph.entry,
        |_, _, transition, is_backward| {
            if !is_backward {
                if let Some(Transition::Rule(handle)) = transition {
                    set.insert(*handle);
                }
                let advances_parser = transition.map_or(false, |t| t.advances_parser());

                !advances_parser
            } else {
                false
            }
        },
    );
    set.iter().copied().collect()
}

fn find_prefix_cycles(
    handle: RuleHandle,
    prefix_children: &HandleVec<RuleHandle, Vec<RuleHandle>>,
    data: &mut SecondaryVec<RuleHandle, Vec<RuleHandle>>,
    visited: &mut HandleBitset<RuleHandle>,
    stack: &mut Vec<RuleHandle>,
) {
    if let Some(pos) = stack.iter().position(|rule| *rule == handle) {
        let mut parent = stack.last().copied().unwrap();
        //      /pos
        // A -> B -> C -> D
        //      ↑_________|
        for &child in &stack[pos..] {
            data.entry(parent).get_or_insert(Vec::new()).push(child);
            parent = child;
        }
        return;
    }

    if visited.insert(handle) {
        return;
    }

    stack.push(handle);
    for &prefix in &prefix_children[handle] {
        find_prefix_cycles(prefix, prefix_children, data, visited, stack);
    }
    stack.pop();
}
