use gnag::{
    ast::RuleKind,
    ctx::ErrorAccumulator,
    handle::{HandleCounter, HandleVec, SecondaryVec, TypedHandle},
    simple_handle,
};

use std::{collections::HashMap, ops::Deref, rc::Rc};

use crate::{
    compile::CompiledFile,
    convert::{ConvertedFile, RuleHandle},
    expr::{Transition, TransitionEffects},
    graph::{NodeHandle, PegNode},
    lower::LoweredFile,
    scope_tree::{ScopeKind, ScopeNodeHandle},
    structure::{mark_used_labels, FlowAction, GraphStructuring, Statement},
};

simple_handle! {
    pub FunctionHandle,
    pub StructHandle,
    pub EnumHandle,
    pub ForeignTypeHandle,
}

impl FunctionHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.functions[self].name
    }
}

impl StructHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.structs[self].name
    }
}

impl EnumHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.enums[self].name
    }
}

impl ForeignTypeHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.foreign_types[self].name
    }
}

#[derive(Default)]
pub struct CodeFile {
    pub functions: HandleVec<FunctionHandle, Function>,
    pub structs: HandleVec<StructHandle, Struct>,
    pub enums: HandleVec<EnumHandle, Enum>,
    pub foreign_types: HandleVec<ForeignTypeHandle, ForeignType>,
}

pub struct InitialItems {
    pub lexer: ForeignTypeHandle,
    pub parser: ForeignTypeHandle,
    pub position: ForeignTypeHandle,
    pub tree_kind: EnumHandle,

    pub tree_kind_name: FunctionHandle,

    pub lexer_save_position: FunctionHandle,
    pub lexer_restore_position: FunctionHandle,
    pub lexer_bytes: FunctionHandle,
    pub lexer_set: FunctionHandle,
    pub lexer_keyword: FunctionHandle,

    pub parser_save_position: FunctionHandle,
    pub parser_restore_position: FunctionHandle,
    pub parser_token: FunctionHandle,
    pub parser_any: FunctionHandle,
    pub parser_not: FunctionHandle,
    pub parser_close_span: FunctionHandle,
}

impl InitialItems {
    pub fn register(module: &mut CodeFile, cx: &CodeFileCx) -> InitialItems {
        let lexer = module.register_foreign_type("Lexer");
        let parser = module.register_foreign_type("Parser");

        let position = module.register_foreign_type("Position");
        let tree_kind = Self::register_tree_kind("TreeKind", module, cx);

        let lexer_arg = ("self", lexer.into());
        let parser_arg = ("self", parser.into());
        let token_arg = ("token", tree_kind.into());
        let bytes_arg = ("bytes", Type::Bytes);

        InitialItems {
            lexer,
            parser,
            position,
            tree_kind,

            tree_kind_name: module.register_function(
                "tree_kind_name",
                &[("self", tree_kind.into())],
                Type::Bytes,
                Self::tree_kind_name_body(tree_kind, cx),
            ),

            lexer_save_position: module.register_foreign_function(
                "save_position",
                &[lexer_arg],
                position,
            ),
            lexer_restore_position: module.register_foreign_function(
                "restore_position",
                &[lexer_arg, ("position", position.into())],
                Type::Unit,
            ),
            lexer_bytes: module.register_foreign_function(
                "bytes",
                &[lexer_arg, bytes_arg],
                Type::Bool,
            ),
            lexer_set: module.register_foreign_function("set", &[lexer_arg, bytes_arg], Type::Bool),
            lexer_keyword: module.register_foreign_function(
                "keyword",
                &[lexer_arg, bytes_arg],
                Type::Bool,
            ),

            parser_save_position: module.register_foreign_function(
                "save_position",
                &[parser_arg],
                position,
            ),
            parser_restore_position: module.register_foreign_function(
                "restore_position",
                &[parser_arg, ("position", position.into())],
                Type::Unit,
            ),
            parser_token: module.register_foreign_function(
                "token",
                &[parser_arg, token_arg],
                Type::Bool,
            ),
            parser_any: module.register_foreign_function("any", &[parser_arg], Type::Bool),
            parser_not: module.register_foreign_function(
                "not",
                &[parser_arg, token_arg],
                Type::Bool,
            ),
            parser_close_span: module.register_foreign_function(
                "close_span",
                &[parser_arg],
                Type::Unit,
            ),
        }
    }
    pub fn register_tree_kind(name: &str, module: &mut CodeFile, cx: &CodeFileCx) -> EnumHandle {
        let variants = cx
            .rule_to_tree_kind_value
            .iter_kv()
            .map(|(rule, enum_value)| (rule.name(&cx.converted).to_owned(), *enum_value as usize))
            .collect();

        module.enums.push(Enum {
            name: name.into(),
            variants,
        })
    }
    pub fn tree_kind_name_body(tree_kind: EnumHandle, cx: &CodeFileCx) -> Expression {
        let branches = cx
            .rule_to_tree_kind_value
            .iter_kv()
            .map(|(rule, enum_variant)| {
                let pattern = Value::EnumVariant(tree_kind, *enum_variant as _);
                let name = Expression::Literal(Value::String(rule.name(&cx.converted).into()));
                (pattern, name)
            })
            .collect();

        Expression::Match {
            condition: Box::new(Expression::AccessArgument(0)),
            branches,
            default: Some(Box::new(Expression::Literal(Value::String(
                "__unknown".into(),
            )))),
        }
    }
}

pub struct CodeFileCx<'a, 'b, 'c> {
    pub err: &'a ErrorAccumulator,
    pub converted: &'b ConvertedFile,
    pub compiled: &'c CompiledFile,
    pub skip_tokens_bound: u16,
    pub rule_to_tree_kind_value: SecondaryVec<RuleHandle, u16>,
}

impl<'a, 'b, 'c> CodeFileCx<'a, 'b, 'c> {
    pub fn new(
        err: &'a ErrorAccumulator,
        converted: &'b ConvertedFile,
        compiled: &'c CompiledFile,
    ) -> CodeFileCx<'a, 'b, 'c> {
        let (bound, collected) = Self::make_tree_kind(converted);
        Self {
            err,
            converted,
            compiled,
            skip_tokens_bound: bound,
            rule_to_tree_kind_value: collected,
        }
    }
    fn make_tree_kind(converted: &ConvertedFile) -> (u16, SecondaryVec<RuleHandle, u16>) {
        // first collect all rules which need handles
        let mut rules = converted
            .rules
            .iter_kv()
            .filter_map(|(handle, rule)| {
                if Some(handle) == converted.lexer {
                    return None;
                }
                Some((
                    rule.kind == RuleKind::Rules,
                    !rule.body.attributes.skip,
                    handle,
                ))
            })
            .collect::<Vec<_>>();

        // do a sort so that token rules are first
        // we can do an unstable sort because all items are distinct due to RuleHandle
        rules.sort_unstable();

        let skip_tokens_count = rules
            .partition_point(|(_, not_skip, _)| !not_skip)
            .try_into()
            .unwrap();

        let mut collected_rules = SecondaryVec::with_capacity(converted.rules.len());

        for (index, (.., rule)) in rules.iter().copied().enumerate() {
            let index: u16 = index.try_into().unwrap();
            collected_rules.insert(rule, index);
        }

        (skip_tokens_count, collected_rules)
    }
}

impl CodeFile {
    pub fn new() -> CodeFile {
        Self::default()
    }
    pub fn register_enum(
        &mut self,
        name: impl Into<String>,
        variants: &[(&str, usize)],
    ) -> EnumHandle {
        let variants = variants
            .into_iter()
            .map(|(a, b)| (a.to_string(), *b))
            .collect();

        self.enums.push(Enum {
            name: name.into(),
            variants,
        })
    }
    pub fn register_function(
        &mut self,
        name: impl Into<String>,
        arguments: &[(&str, Type)],
        ret: impl Into<Type>,
        body: Expression,
    ) -> FunctionHandle {
        let arguments = arguments
            .into_iter()
            .map(|(a, b)| (a.to_string(), *b))
            .collect();

        self.functions.push(Function {
            name: name.into(),
            arguments,
            return_type: ret.into(),
            body: Some(body),
        })
    }
    pub fn register_foreign_function(
        &mut self,
        name: impl Into<String>,
        arguments: &[(&str, Type)],
        ret: impl Into<Type>,
    ) -> FunctionHandle {
        let arguments = arguments
            .into_iter()
            .map(|(a, b)| (a.to_string(), *b))
            .collect();

        self.functions.push(Function {
            name: name.into(),
            arguments,
            return_type: ret.into(),
            body: None,
        })
    }
    pub fn register_foreign_type(&mut self, name: impl Into<String>) -> ForeignTypeHandle {
        self.foreign_types.push(ForeignType { name: name.into() })
    }

    pub fn register_types(&mut self, cx: &CodeFileCx) -> InitialItems {
        InitialItems::register(self, cx)
    }
    pub fn register_rules(&mut self, items: &InitialItems, cx: &CodeFileCx) {
        let mut statements = Vec::new();
        for (handle, rule) in cx.compiled.rules.iter_kv() {
            let nodes = &rule.nodes;

            let structuring = GraphStructuring::new(nodes);
            structuring.emit_code(&mut statements, true, true, nodes);

            let body = unflatten_to_expression(&statements, nodes, |transition| match transition {
                Transition::Error => todo!(),
                Transition::ByteSet(_) => todo!(),
                Transition::Bytes(_) => todo!(),
                Transition::Keyword(_) => todo!(),
                Transition::Rule(_) => todo!(),
                Transition::PrattRule(_, _) => todo!(),
                Transition::CompareBindingPower(_) => todo!(),
                Transition::Any => todo!(),
                Transition::Not(_) => todo!(),
                Transition::SaveState(_) => todo!(),
                Transition::RestoreState(_) => todo!(),
                Transition::CloseSpan(_) => todo!(),
                Transition::Return(_) => todo!(),
                Transition::Dummy(_) => todo!(),
            });

            let name = handle.name(&cx.converted);
            self.functions.push(Function {
                name: name.to_owned(),
                arguments: (),
                return_type: (),
                body: (),
            });
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ItemType {
    Struct(StructHandle),
    Enum(EnumHandle),
    Foreign(ForeignTypeHandle),
}

#[derive(Clone, Copy, Debug)]
pub enum Type {
    Bool,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Bytes,
    String,
    TreeKind,
    Unit,
    Item(ItemType),
}

// implement From directly, rather than relying on Handle->ItemType->Type
// which cannot be inferred
impl From<StructHandle> for Type {
    fn from(value: StructHandle) -> Self {
        Type::Item(ItemType::Struct(value))
    }
}

impl From<EnumHandle> for Type {
    fn from(value: EnumHandle) -> Self {
        Type::Item(ItemType::Enum(value))
    }
}

impl From<ForeignTypeHandle> for Type {
    fn from(value: ForeignTypeHandle) -> Self {
        Type::Item(ItemType::Foreign(value))
    }
}

impl From<ItemType> for Type {
    fn from(value: ItemType) -> Self {
        Self::Item(value)
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    EnumVariant(EnumHandle, u32),
    Bytes(Rc<[u8]>),
    String(Rc<str>),
    Unit,
}

impl Value {
    #[allow(unused_must_use)]
    pub fn display(&self, buf: &mut dyn std::fmt::Write, module: &CodeFile) {
        match self {
            Value::U8(a) => write!(buf, "{a}"),
            Value::U16(a) => write!(buf, "{a}"),
            Value::U32(a) => write!(buf, "{a}"),
            Value::U64(a) => write!(buf, "{a}"),
            Value::I8(a) => write!(buf, "{a}"),
            Value::I16(a) => write!(buf, "{a}"),
            Value::I32(a) => write!(buf, "{a}"),
            Value::I64(a) => write!(buf, "{a}"),
            Value::EnumVariant(a, index) => {
                let name = a.name(module);
                let (variant, _) = &module.enums[*a].variants[*index as usize];
                write!(buf, "{name}::{variant}")
            }
            Value::String(a) => {
                let deref: &str = &*a;
                write!(buf, "{:?}", deref)
            }
            Value::Unit => write!(buf, "()"),
            Value::Bytes(a) => {
                // https://users.rust-lang.org/t/how-to-print-the-byte-string-literal-of-a-bytes/78910/5
                for &b in a.iter() {
                    if b >= 40 && b <= 126 {
                        buf.write_char(std::char::from_u32(b as u32).unwrap());
                    } else {
                        write!(buf, "\\x{b:02X}").unwrap();
                    }
                }
                Ok(())
            }
        };
    }
}

simple_handle! {
    pub BlockLabel,
    pub VariableHandle,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub statements: Rc<[Expression]>,
}

impl Block {
    pub fn new(item: Expression) -> Block {
        Self {
            statements: Rc::new([item]),
        }
    }
}

impl FromIterator<Expression> for Block {
    fn from_iter<T: IntoIterator<Item = Expression>>(iter: T) -> Self {
        Self {
            statements: iter.into_iter().collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(Value),
    Call {
        handle: FunctionHandle,
        arguments: Vec<Expression>,
    },
    Panic(String),
    Block(Option<BlockLabel>, Block),
    Loop(Option<BlockLabel>, Block),
    If {
        condition: Box<Expression>,
        pass: Block,
        fail: Option<Block>,
    },
    Match {
        condition: Box<Expression>,
        branches: Vec<(Value, Expression)>,
        default: Option<Box<Expression>>,
    },
    While {
        label: Option<BlockLabel>,
        condition: Box<Expression>,
        block: Block,
    },
    Negate(Box<Expression>),
    Break(Option<BlockLabel>),
    Continue(Option<BlockLabel>),
    Return,
    DeclareVariable {
        handle: VariableHandle,
        name: String,
        _type: Type,
        value: Option<Box<Expression>>,
    },
    StoreVariable(VariableHandle, Box<Expression>),
    AccessVariable(VariableHandle),
    AccessArgument(u32),
}

impl Expression {
    #[allow(unused_must_use)]
    pub fn display(&self, buf: &mut dyn std::fmt::Write, module: &CodeFile, cx: &CodeFileCx) {
        fn display_block(
            label: Option<BlockLabel>,
            block: &Block,
            keyword: Option<&str>,
            condition: Option<&Expression>,
            buf: &mut dyn std::fmt::Write,
            cx: &CodeFileCx,
            module: &CodeFile,
        ) {
            if let Some(label) = label {
                write!(buf, "'b{}: ", label.index());
            }
            if let Some(keyword) = keyword {
                write!(buf, "{keyword}");
            }

            if let Some(condition) = condition {
                condition.display(buf, module, cx);
                write!(buf, " ");
            }

            write!(buf, "{{\n");
            for a in block.statements.iter() {
                a.display(buf, module, cx);
                write!(buf, ";\n");
            }
            write!(buf, "}}\n");
        }

        fn break_or_return(
            buf: &mut dyn std::fmt::Write,
            keyword: &str,
            label: &Option<BlockLabel>,
        ) {
            write!(buf, "{keyword}");
            if let Some(label) = label {
                write!(buf, " 'b{}", label.index());
            }
        }

        match self {
            Expression::Literal(l) => l.display(buf, module),
            Expression::Call { handle, arguments } => {
                let name = handle.name(module);
                write!(buf, "{name}(");
                for a in arguments {
                    a.display(buf, module, cx);
                    write!(buf, ", ");
                }
                write!(buf, ")");
            }
            Expression::Panic(msg) => {
                write!(buf, "panic!({msg:?})");
            }
            Expression::Block(label, block) => {
                display_block(*label, block, None, None, buf, cx, module);
            }
            Expression::Loop(label, block) => {
                display_block(*label, block, Some("loop"), None, buf, cx, module);
            }
            Expression::If {
                condition,
                pass,
                fail,
            } => {
                display_block(None, pass, Some("true"), Some(condition), buf, cx, module);
                if let Some(fail) = fail {
                    // special case 'if .. {} else if .. {}' formatting
                    display_block(None, fail, Some("else"), None, buf, cx, module);
                }
            }
            Expression::Match {
                condition,
                branches,
                default,
            } => {
                write!(buf, "match ");
                condition.display(buf, module, cx);

                write!(buf, "{{\n");
                for (branch, result) in branches {
                    branch.display(buf, module);
                    write!(buf, " => ");
                    result.display(buf, module, cx);
                    write!(buf, ",\n");
                }
                if let Some(default) = default {
                    write!(buf, "_ => ");
                    default.display(buf, module, cx);
                    write!(buf, ",\n");
                }
                write!(buf, "}}\n");
            }
            Expression::While {
                label,
                condition,
                block,
            } => {
                display_block(
                    *label,
                    block,
                    Some("while"),
                    Some(condition),
                    buf,
                    cx,
                    module,
                );
            }
            Expression::Negate(expr) => {
                write!(buf, "!(");
                expr.display(buf, module, cx);
                write!(buf, ")");
            }
            Expression::Break(label) => {
                break_or_return(buf, "break", label);
            }
            Expression::Continue(label) => {
                break_or_return(buf, "continue", label);
            }
            Expression::Return => {
                write!(buf, "return");
            }
            Expression::DeclareVariable {
                handle,
                name: _,
                _type,
                value,
            } => {
                write!(buf, "let v{}", handle.index());
                if let Some(value) = value {
                    write!(buf, " = ");
                    value.display(buf, module, cx);
                }
            }
            Expression::StoreVariable(handle, value) => {
                write!(buf, "let v{} = ", handle.index());
                value.display(buf, module, cx);
            }
            Expression::AccessVariable(handle) => {
                write!(buf, "v{}", handle.index());
            }
            Expression::AccessArgument(index) => {
                write!(buf, "argument{index}");
            }
        }
    }
}

pub struct Function {
    pub name: String,
    pub arguments: Vec<(String, Type)>,
    pub return_type: Type,
    pub body: Option<Expression>,
}

pub struct Struct {
    pub name: String,
    pub fields: Vec<(String, Type)>,
}

pub struct Enum {
    pub name: String,
    pub variants: Vec<(String, usize)>,
}

pub struct ForeignType {
    pub name: String,
}

fn unflatten_to_expression(
    statements: &[Statement],
    nodes: &HandleVec<NodeHandle, PegNode>,
    mut transition_to_expression: impl FnMut(&Transition) -> Expression,
) -> Expression {
    let used_labels = mark_used_labels(statements, &mut Vec::new());

    let mut scope_counter = HandleCounter::new();
    let mut compacted_scopes: HashMap<ScopeNodeHandle, BlockLabel> = Default::default();

    let mut scope_stack = Vec::new();
    let mut scope_statements = Vec::new();

    for statement in statements {
        match statement {
            Statement::Open(block) => {
                let needs_scope = used_labels.contains(block.handle);
                let scope = needs_scope.then(|| {
                    let next = scope_counter.next();
                    compacted_scopes.insert(block.handle, next);
                    next
                });

                scope_stack.push((block, scope, scope_statements.len()));
            }
            &Statement::Statement {
                condition,
                mut success,
                mut fail,
            } => {
                let transition = &nodes[condition].transition;
                let effects = transition.effects();

                let (current_scope, ..) = scope_stack.last().unwrap();

                let convert_action = |action: FlowAction| -> Option<Expression> {
                    match action {
                        FlowAction::None => None,
                        FlowAction::Break(_) | FlowAction::Continue(_) => {
                            let scope = action
                                .flow_target_scope_if_needed(current_scope)
                                .map(|a| compacted_scopes[&a]);

                            if let FlowAction::Break(_) = action {
                                Some(Expression::Break(scope))
                            } else {
                                Some(Expression::Continue(scope))
                            }
                        }
                        FlowAction::Panic => {
                            Some(Expression::Panic("Dangling control flow".into()))
                        }
                    }
                };

                if let Transition::Dummy(should_succeed) = transition {
                    let action = match should_succeed {
                        true => success,
                        false => fail,
                    };
                    scope_statements.extend(convert_action(action));
                    continue;
                }

                let converted_transition: Expression = transition_to_expression(transition);

                match effects {
                    TransitionEffects::Fallible => {}
                    // fudge the action values to get the needed behaviour in a single code path
                    TransitionEffects::Infallible => {
                        fail = success;
                    }
                    TransitionEffects::Noreturn => {
                        success = FlowAction::None;
                        fail = FlowAction::None;
                    }
                }

                match (success, fail) {
                    (FlowAction::None, FlowAction::None) => {
                        scope_statements.push(converted_transition);
                    }
                    (_, _) => {
                        if success == fail {
                            scope_statements.push(converted_transition);
                            scope_statements.extend(convert_action(success));
                        } else {
                            let mut condition = Box::new(converted_transition);

                            if success == FlowAction::None {
                                debug_assert!(fail != FlowAction::None);
                                condition = Box::new(Expression::Negate(condition));
                                std::mem::swap(&mut success, &mut fail);
                            }

                            scope_statements.push(Expression::If {
                                condition,
                                pass: convert_action(success).map(Block::new).unwrap(),
                                fail: convert_action(fail).map(Block::new),
                            });
                        }
                    }
                }
            }
            Statement::Close => {
                let (scope, label, start_index) = scope_stack.pop().unwrap();
                let block = scope_statements.drain(start_index..).collect();

                let condition = scope.condition.map(|condition| {
                    let transition = &nodes[condition.condition].transition;
                    let converted_transition: Expression = transition_to_expression(transition);

                    let mut expr = Box::new(converted_transition);
                    if condition.negate {
                        expr = Box::new(Expression::Negate(expr));
                    }

                    expr
                });

                let block_expression = match scope.kind {
                    ScopeKind::Block => {
                        if let Some(condition) = condition {
                            let body = match label {
                                Some(_) => Block::new(Expression::Block(label, block)),
                                None => block,
                            };

                            Expression::If {
                                condition,
                                pass: body,
                                fail: None,
                            }
                        } else {
                            Expression::Block(label, block)
                        }
                    }
                    ScopeKind::Loop => {
                        if let Some(condition) = condition {
                            Expression::While {
                                label,
                                condition,
                                block,
                            }
                        } else {
                            Expression::Loop(label, block)
                        }
                    }
                };

                scope_statements.push(block_expression);
            }
        }
    }

    assert!(scope_stack.is_empty());
    assert_eq!(scope_statements.len(), 1);

    scope_statements.pop().unwrap()
}
