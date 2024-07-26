use gnag::{
    ast::RuleKind,
    ctx::ErrorAccumulator,
    handle::{HandleBitset, HandleVec, SecondaryVec, TypedHandle},
    simple_handle,
};

use std::{collections::HashMap, rc::Rc};

use crate::{
    compile::CompiledFile,
    convert::{ConvertedFile, RuleHandle},
    expr::{self, RuleExpr, Transition, TransitionEffects},
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
    pub fn as_type(self) -> Type {
        Type::Item(ItemType::Struct(self))
    }
}

impl EnumHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.enums[self].name
    }
    pub fn as_type(self) -> Type {
        Type::Item(ItemType::Enum(self))
    }
}

impl ForeignTypeHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.foreign_types[self].name
    }
    pub fn as_type(self) -> Type {
        Type::Item(ItemType::Foreign(self))
    }
}

pub struct InitialItems {
    pub lexer: Type,
    pub parser: Type,
    pub lexer_position: ForeignTypeHandle,
    pub parser_position: ForeignTypeHandle,

    pub tree_kind: EnumHandle,
    pub tree_kind_name: FunctionHandle,
    pub tree_kind_is_skip: FunctionHandle,
    pub tree_kind_is_token: FunctionHandle,

    pub lexer_save_position: FunctionHandle,
    pub lexer_restore_position: FunctionHandle,
    pub lexer_close_span: FunctionHandle,

    pub lexer_bytes: FunctionHandle,
    pub lexer_set: FunctionHandle,
    pub lexer_keyword: FunctionHandle,
    pub lexer_any: FunctionHandle,
    pub lexer_not: FunctionHandle,

    pub parser_save_position: FunctionHandle,
    pub parser_restore_position: FunctionHandle,
    pub parser_close_span: FunctionHandle,

    pub parser_token: FunctionHandle,
    pub parser_any: FunctionHandle,
    pub parser_not: FunctionHandle,
}

impl InitialItems {
    pub fn register(module: &mut CodeFile, cx: &CodeFileCx) -> InitialItems {
        let lexer = module.register_foreign_type("Lexer").as_type().ref_mut_of();
        let parser = module
            .register_foreign_type("Parser")
            .as_type()
            .ref_mut_of();

        let lexer_position = module.register_foreign_type("LexerPosition");
        let parser_position = module.register_foreign_type("ParserPosition");
        let tree_kind = Self::register_tree_kind("TreeKind", module, cx);

        let lexer_arg = ("self", &lexer);
        let parser_arg = ("self", &parser);
        let lexer_position_arg = ("position", &lexer_position.as_type());
        let parser_position_arg = ("position", &parser_position.as_type());
        let token_arg = ("token", &tree_kind.as_type());
        let bytes_arg = ("bytes", &Type::Bytes);

        InitialItems {
            tree_kind,
            tree_kind_name: module.register_function(
                "tree_kind_name",
                &[("self", tree_kind.into())],
                Type::String,
                Self::name_of_variant_function_body(tree_kind, &module),
            ),
            tree_kind_is_skip: module.register_function(
                "tree_kind_name",
                &[("self", tree_kind.into())],
                Type::String,
                Self::name_of_variant_function_body(tree_kind, &module),
            ),
            tree_kind_is_token: module.register_function(
                "tree_kind_name",
                &[("self", tree_kind.into())],
                Type::String,
                Self::name_of_variant_function_body(tree_kind, &module),
            ),
            lexer_save_position: module.declare_function(
                "save_position",
                &[lexer_arg],
                lexer_position,
            ),
            lexer_restore_position: module.declare_function(
                "restore_position",
                &[lexer_arg, lexer_position_arg],
                Type::Unit,
            ),
            lexer_close_span: module.declare_function(
                "close_span",
                &[lexer_arg, lexer_position_arg],
                Type::Unit,
            ),

            lexer_bytes: module.declare_function("bytes", &[lexer_arg, bytes_arg], Type::Bool),
            lexer_set: module.declare_function("set", &[lexer_arg, bytes_arg], Type::Bool),
            lexer_keyword: module.declare_function("keyword", &[lexer_arg, bytes_arg], Type::Bool),
            lexer_any: module.declare_function("any", &[lexer_arg], Type::Bool),
            lexer_not: module.declare_function("not", &[lexer_arg], Type::Bool),
            parser_save_position: module.declare_function(
                "save_position",
                &[parser_arg],
                parser_position,
            ),

            parser_restore_position: module.declare_function(
                "restore_position",
                &[parser_arg, parser_position_arg],
                Type::Unit,
            ),
            parser_close_span: module.declare_function(
                "close_span",
                &[parser_arg, parser_position_arg],
                Type::Unit,
            ),
            parser_token: module.declare_function("token", &[parser_arg, token_arg], Type::Bool),
            parser_any: module.declare_function("any", &[parser_arg], Type::Bool),
            parser_not: module.declare_function("not", &[parser_arg, token_arg], Type::Bool),

            lexer,
            parser,
            lexer_position,
            parser_position,
        }
    }
    pub fn register_tree_kind(name: &str, module: &mut CodeFile, cx: &CodeFileCx) -> EnumHandle {
        let mut variants = cx
            .rule_to_tree_kind_value
            .iter_kv()
            .map(|(rule, enum_value)| (rule.name(&cx.converted).to_owned(), *enum_value as usize))
            .collect::<Vec<_>>();

        variants.sort_by_key(|(_, value)| *value);

        module.enums.push(Enum {
            name: name.into(),
            variants,
        })
    }
    pub fn name_of_variant_function_body(handle: EnumHandle, module: &CodeFile) -> FunctionBody {
        let item = &module.enums[handle];
        let branches = item
            .variants
            .iter()
            .enumerate()
            .map(|(variant_index, (name, _))| {
                let pattern = Value::EnumVariant(handle, variant_index as u32);
                let name = Expression::Value(Value::String(name.as_str().into()));
                (pattern, name)
            })
            .collect();

        let expression = Expression::Match {
            condition: Box::new(Expression::AccessArgument(0)),
            branches,
            default: Some(Box::new(Expression::Value(Value::String(
                "__unknown".into(),
            )))),
        };

        FunctionBody {
            variables: HandleVec::new(),
            expr: expression,
        }
    }

    pub fn rule_class_type(&self, kind: RuleKind) -> &Type {
        match kind {
            RuleKind::Tokens => &self.lexer,
            RuleKind::Rules => &self.parser,
        }
    }
}

pub struct CodeFileCx<'a, 'b, 'c> {
    pub err: &'a ErrorAccumulator,
    pub converted: &'b ConvertedFile,
    pub compiled: &'c CompiledFile,
    pub skip_tokens_bound: u16,
    pub tokens_bound: u16,
    pub rule_to_tree_kind_value: SecondaryVec<RuleHandle, u32>,
}

impl<'a, 'b, 'c> CodeFileCx<'a, 'b, 'c> {
    pub fn new(
        err: &'a ErrorAccumulator,
        converted: &'b ConvertedFile,
        compiled: &'c CompiledFile,
    ) -> CodeFileCx<'a, 'b, 'c> {
        let (skip_tokens_bound, tokens_bound, collected) = Self::make_tree_kind(converted);

        Self {
            err,
            converted,
            compiled,
            skip_tokens_bound,
            tokens_bound,
            rule_to_tree_kind_value: collected,
        }
    }
    fn make_tree_kind(converted: &ConvertedFile) -> (u16, u16, SecondaryVec<RuleHandle, u32>) {
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

        let tokens_count = rules
            .partition_point(|(is_rules, _, _)| *is_rules)
            .try_into()
            .unwrap();

        let mut collected_rules = SecondaryVec::with_capacity(converted.rules.len());

        for (index, (.., rule)) in rules.iter().copied().enumerate() {
            let index: u32 = index.try_into().unwrap();
            collected_rules.insert(rule, index);
        }

        (skip_tokens_count, tokens_count, collected_rules)
    }
}

#[derive(Default)]
pub struct CodeFile {
    pub functions: HandleVec<FunctionHandle, Function>,
    pub structs: HandleVec<StructHandle, Struct>,
    pub enums: HandleVec<EnumHandle, Enum>,
    pub foreign_types: HandleVec<ForeignTypeHandle, ForeignType>,
}

impl CodeFile {
    pub fn empty() -> CodeFile {
        Self::default()
    }
    pub fn new(
        err: &ErrorAccumulator,
        converted: &ConvertedFile,
        compiled: &CompiledFile,
    ) -> CodeFile {
        let mut this = Self::empty();
        let cx = CodeFileCx::new(err, converted, compiled);

        let items = InitialItems::register(&mut this, &cx);
        RuleToFunctionBuilder::register(&mut this, &items, &cx);

        this
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
        body: FunctionBody,
    ) -> FunctionHandle {
        let arguments = arguments
            .into_iter()
            .map(|(a, b)| (a.to_string(), b.clone()))
            .collect();

        self.functions.push(Function {
            name: name.into(),
            arguments,
            return_type: ret.into(),
            body: Some(body),
        })
    }
    pub fn declare_function(
        &mut self,
        name: impl Into<String>,
        arguments: &[(&str, &Type)],
        ret: impl Into<Type>,
    ) -> FunctionHandle {
        let arguments = arguments
            .into_iter()
            .copied()
            .map(|(a, b)| (a.to_string(), b.clone()))
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

    #[allow(unused_must_use)]
    pub fn display(&self, buf: &mut dyn std::fmt::Write) {
        for body in &self.foreign_types {
            let name = &body.name;
            writeln!(buf, "/// extern type {name}");
        }

        for function in &self.functions {
            if function.body.is_none() {
                write!(buf, "/// extern ");
                self.display_function(buf, function);
                write!(buf, "\n");
            }
        }

        for body in &self.structs {
            let name = &body.name;
            write!(buf, "pub struct {name} {{\n");
            for (name, _type) in &body.fields {
                write!(buf, "    {name}: ");
                _type.display(buf, self);
                write!(buf, ",\n");
            }
            write!(buf, "}}\n");
        }

        for body in &self.enums {
            let name = &body.name;
            write!(buf, "pub enum {name} {{\n",);
            for (name, value) in &body.variants {
                write!(buf, "    {name} = {value},\n");
            }
            write!(buf, "}}\n");
        }

        for function in &self.functions {
            if let Some(body) = &function.body {
                write!(buf, "pub ");
                self.display_function(buf, function);
                let is_block = matches!(body.expr, Expression::Block(..));
                if !is_block {
                    write!(buf, " {{\n");
                }
                body.expr.display(buf, self, Some(body));
                if !is_block {
                    write!(buf, "\n}}");
                }
                write!(buf, "\n");
            }
        }
    }

    #[allow(unused_must_use)]
    fn display_function(&self, buf: &mut dyn std::fmt::Write, function: &Function) {
        write!(buf, "fn {}(", function.name);
        let mut first = true;
        for (name, _type) in &function.arguments {
            if !first {
                write!(buf, ", ");
            }
            first = false;
            write!(buf, "{name}: ");
            _type.display(buf, self);
        }
        write!(buf, ")");
        if function.return_type != Type::Unit {
            write!(buf, " -> ");
            function.return_type.display(buf, self);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemType {
    Struct(StructHandle),
    Enum(EnumHandle),
    Foreign(ForeignTypeHandle),
}

impl ItemType {
    pub fn name(self, module: &CodeFile) -> &str {
        match self {
            ItemType::Struct(a) => a.name(module),
            ItemType::Enum(a) => a.name(module),
            ItemType::Foreign(a) => a.name(module),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
    Unit,
    Item(ItemType),
    Ref(Box<Type>),
    RefMut(Box<Type>),
}

impl Type {
    #[allow(unused_must_use)]
    pub fn display(&self, buf: &mut dyn std::fmt::Write, module: &CodeFile) {
        let name = match self {
            Type::Bool => "bool",
            Type::U8 => "u8",
            Type::U16 => "u16",
            Type::U32 => "u32",
            Type::U64 => "u64",
            Type::I8 => "i8",
            Type::I16 => "i16",
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::Bytes => "&[u8]",
            Type::String => "&str",
            Type::Unit => "()",
            Type::Item(item) => item.name(module),
            Type::Ref(inner) => {
                write!(buf, "&");
                inner.display(buf, module);
                return;
            }
            Type::RefMut(inner) => {
                write!(buf, "&mut ");
                inner.display(buf, module);
                return;
            }
        };
        write!(buf, "{name}");
    }
    pub fn ref_of(self) -> Type {
        Type::Ref(Box::new(self))
    }
    pub fn ref_mut_of(self) -> Type {
        Type::RefMut(Box::new(self))
    }
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
    Bool(bool),
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
            Value::Bool(a) => write!(buf, "{a}"),
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
                write!(buf, "\"");
                for c in a.iter().copied() {
                    write!(buf, "{}", std::ascii::escape_default(c));
                }
                write!(buf, "\"");
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
pub enum BinaryOp {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
}

#[derive(Clone, Debug)]
pub enum UnaryOp {
    Negate,
}

#[derive(Clone, Debug)]
pub enum Expression {
    Error,
    Value(Value),
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
    Binary {
        op: BinaryOp,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expression>,
    },
    Break(Option<BlockLabel>),
    Continue(Option<BlockLabel>),
    Return(Option<Box<Expression>>),
    DeclareVariable {
        handle: VariableHandle,
        value: Option<Box<Expression>>,
    },
    StoreVariable(VariableHandle, Box<Expression>),
    AccessVariable(VariableHandle),
    AccessArgument(u32),
}

impl From<Value> for Expression {
    fn from(value: Value) -> Self {
        Expression::Value(value)
    }
}

impl Expression {
    #[allow(unused_must_use)]
    pub fn display(
        &self,
        buf: &mut dyn std::fmt::Write,
        module: &CodeFile,
        function: Option<&FunctionBody>,
    ) {
        fn display_block(
            label: Option<BlockLabel>,
            block: &Block,
            keyword: Option<&str>,
            condition: Option<&Expression>,
            buf: &mut dyn std::fmt::Write,
            // cx: &CodeFileCx,
            module: &CodeFile,
            function: Option<&FunctionBody>,
        ) {
            if let Some(label) = label {
                write!(buf, "'b{}: ", label.index());
            }
            if let Some(keyword) = keyword {
                write!(buf, "{keyword} ");
            }

            if let Some(condition) = condition {
                condition.display(buf, module, function);
                write!(buf, " ");
            }

            write!(buf, "{{\n");
            for a in block.statements.iter() {
                a.display(buf, module, function);
                write!(buf, ";\n");
            }
            write!(buf, "}}");
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
            Expression::Error => {
                write!(buf, r#"unreachable!("Error")"#);
            }
            Expression::Value(l) => {
                l.display(buf, module);
            }
            Expression::Call { handle, arguments } => {
                let name = handle.name(module);
                write!(buf, "{name}(");
                for a in arguments {
                    a.display(buf, module, function);
                    write!(buf, ", ");
                }
                write!(buf, ")");
            }
            Expression::Panic(msg) => {
                write!(buf, "panic!({msg:?})");
            }
            Expression::Block(label, block) => {
                display_block(*label, block, None, None, buf, module, function);
            }
            Expression::Loop(label, block) => {
                display_block(*label, block, Some("loop"), None, buf, module, function);
            }
            Expression::If {
                condition,
                pass,
                fail,
            } => {
                display_block(
                    None,
                    pass,
                    Some("if"),
                    Some(condition),
                    buf,
                    module,
                    function,
                );
                if let Some(fail) = fail {
                    display_block(None, fail, Some("else"), None, buf, module, function);
                }
            }
            Expression::Match {
                condition,
                branches,
                default,
            } => {
                write!(buf, "match ");
                condition.display(buf, module, function);

                write!(buf, " {{\n");
                for (branch, result) in branches {
                    write!(buf, "    ");
                    branch.display(buf, module);
                    write!(buf, " => ");
                    result.display(buf, module, function);
                    write!(buf, ",\n");
                }
                if let Some(default) = default {
                    write!(buf, "_ => ");
                    default.display(buf, module, function);
                    write!(buf, ",\n");
                }
                write!(buf, "}}");
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
                    module,
                    function,
                );
            }
            Expression::Binary { op, left, right } => {
                let op = match op {
                    BinaryOp::Less => "<",
                    BinaryOp::LessEqual => "<=",
                    BinaryOp::Greater => ">",
                    BinaryOp::GreaterEqual => ">=",
                    BinaryOp::Equal => "==",
                    BinaryOp::NotEqual => "!=",
                };
                write!(buf, "(");
                left.display(buf, module, function);
                write!(buf, " {op} ");
                right.display(buf, module, function);
                write!(buf, ")");
            }
            Expression::Unary { op, expr } => {
                let op = match op {
                    UnaryOp::Negate => "!",
                };
                write!(buf, "({op}");
                expr.display(buf, module, function);
                write!(buf, ")");
            }
            Expression::Break(label) => {
                break_or_return(buf, "break", label);
            }
            Expression::Continue(label) => {
                break_or_return(buf, "continue", label);
            }
            Expression::Return(value) => {
                write!(buf, "return");
                if let Some(value) = value {
                    write!(buf, " ");
                    value.display(buf, module, function);
                }
            }
            Expression::DeclareVariable { handle, value } => {
                let (name, type_) = &function.unwrap().variables[*handle];

                write!(buf, "let {name}: ");
                type_.display(buf, module);

                if let Some(value) = value {
                    write!(buf, " = ");
                    value.display(buf, module, function);
                }
            }
            Expression::StoreVariable(handle, value) => {
                write!(buf, "let v{} = ", handle.index());
                value.display(buf, module, function);
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
    pub body: Option<FunctionBody>,
}

pub struct FunctionBody {
    pub variables: HandleVec<VariableHandle, (String, Type)>,
    pub expr: Expression,
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

#[derive(Default)]
struct RemapHandles {
    compact_counter: u32,
    sparse_mapping: HashMap<u32, u32>,
}

impl RemapHandles {
    fn insert(&mut self, handle: u32) -> u32 {
        let Self {
            compact_counter,
            sparse_mapping,
        } = self;

        let next = *compact_counter;
        *compact_counter += 1;

        let previous = sparse_mapping.insert(handle, next);
        assert!(previous.is_none());

        next
    }
    fn get(&self, handle: u32) -> u32 {
        self.sparse_mapping[&handle]
    }
    fn clear(&mut self) {
        self.compact_counter = 0;
        self.sparse_mapping.clear();
    }
}

#[derive(Default)]
struct RuleToFunctionBuilder {
    is_pratt_rule: HandleBitset<RuleHandle>,
    function_handles: HandleVec<RuleHandle, FunctionHandle>,
    // per-function data
    variables: HandleVec<VariableHandle, (String, Type)>,
    sparse_variables: HashMap<expr::VariableHandle, VariableHandle>,
    compact_scopes: RemapHandles,
    scope_statements: Vec<Expression>,
}

impl RuleToFunctionBuilder {
    fn register(module: &mut CodeFile, items: &InitialItems, cx: &CodeFileCx) {
        let is_pratt_rule = Self::make_is_pratt(cx.converted);

        let mut this = Self {
            function_handles: Self::declare_functions(&is_pratt_rule, cx, items, module),
            is_pratt_rule,
            ..Default::default()
        };

        for handle in cx.compiled.rules.iter_keys() {
            let body = this.convert_rule(handle, items, cx);

            let reserved = this.function_handles[handle];
            let function = &mut module.functions[reserved];
            function.body = Some(body);
        }
    }
    fn declare_functions(
        is_pratt_rule: &HandleBitset<RuleHandle>,
        cx: &CodeFileCx,
        items: &InitialItems,
        module: &mut CodeFile,
    ) -> HandleVec<RuleHandle, FunctionHandle> {
        cx.converted.rules.map_ref_with_key(|handle, rule| {
            let name = match rule.kind {
                RuleKind::Tokens => "l",
                RuleKind::Rules => "p",
            };
            let object = items.rule_class_type(rule.kind);
            let args = [(name, object), ("min_bp", &Type::U32)];
            let args = match is_pratt_rule.contains(handle) {
                true => &args[..],
                false => &args[..1],
            };
            module.declare_function(rule.body.name.clone(), args, Type::Bool)
        })
    }
    fn make_is_pratt(converted: &ConvertedFile) -> HandleBitset<RuleHandle> {
        let mut is_pratt_rule = HandleBitset::with_capacity_filled(converted.rules.len(), false);

        for (handle, rule) in converted.rules.iter_kv() {
            if let RuleExpr::Pratt(_) = rule.body.expr {
                is_pratt_rule.insert(handle);
            }
        }

        is_pratt_rule
    }
    fn add_variable(
        &mut self,
        sparse_handle: expr::VariableHandle,
        name: &str,
        type_: Type,
    ) -> VariableHandle {
        let handle = self.variables.push((name.to_owned(), type_));
        let previous = self.sparse_variables.insert(sparse_handle, handle);
        assert!(previous.is_none());
        handle
    }
    fn get_variable(&self, handle: expr::VariableHandle) -> VariableHandle {
        *self.sparse_variables.get(&handle).unwrap()
    }
    fn insert_scope_label(&mut self, handle: ScopeNodeHandle) -> BlockLabel {
        let compact = self.compact_scopes.insert(handle.index_u32());
        BlockLabel(compact)
    }
    fn get_scope_label(&self, handle: ScopeNodeHandle) -> BlockLabel {
        let compact = self.compact_scopes.get(handle.index_u32());
        BlockLabel(compact)
    }
    fn convert_rule(
        &mut self,
        handle: RuleHandle,
        items: &InitialItems,
        cx: &CodeFileCx,
    ) -> FunctionBody {
        self.variables.clear();
        self.sparse_variables.clear();
        self.compact_scopes.clear();
        self.scope_statements.clear();

        let converted_rule = &cx.converted.rules[handle];
        let kind = converted_rule.kind;

        let nodes = &cx.compiled.rules[handle].nodes;

        let structuring = GraphStructuring::new(nodes);
        let statements = structuring.emit_code(true, true, nodes);

        let used_labels = mark_used_labels(&statements, &mut Vec::new());
        let mut scope_stack = Vec::new();

        for statement in &statements {
            match statement {
                Statement::Open(block) => {
                    let needs_scope = used_labels.contains(block.handle);
                    let scope = needs_scope.then(|| self.insert_scope_label(block.handle));
                    scope_stack.push((block, scope, self.scope_statements.len()));
                }
                &Statement::Statement {
                    condition,
                    mut success,
                    mut fail,
                } => {
                    let transition = &nodes[condition].transition;
                    let effects = transition.effects();

                    let (current_scope, ..) = scope_stack.last().unwrap();

                    let convert_action = |builder: &RuleToFunctionBuilder,
                                          action: FlowAction|
                     -> Option<Expression> {
                        match action {
                            FlowAction::None => None,
                            FlowAction::Break(_) | FlowAction::Continue(_) => {
                                let scope = action
                                    .flow_target_scope_if_needed(current_scope)
                                    .map(|a| builder.get_scope_label(a));

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
                        self.scope_statements.extend(convert_action(self, action));
                        continue;
                    }

                    let converted_transition: Expression =
                        self.convert_transition(kind, transition, items, cx);

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
                            self.scope_statements.push(converted_transition);
                        }
                        (_, _) => {
                            if success == fail {
                                self.scope_statements.push(converted_transition);
                                self.scope_statements.extend(convert_action(self, success));
                            } else {
                                let mut condition = Box::new(converted_transition);

                                if success == FlowAction::None {
                                    debug_assert!(fail != FlowAction::None);
                                    condition = Box::new(Expression::Unary {
                                        op: UnaryOp::Negate,
                                        expr: condition,
                                    });
                                    std::mem::swap(&mut success, &mut fail);
                                }

                                self.scope_statements.push(Expression::If {
                                    condition,
                                    pass: convert_action(self, success).map(Block::new).unwrap(),
                                    fail: convert_action(self, fail).map(Block::new),
                                });
                            }
                        }
                    }
                }
                Statement::Close => {
                    let (scope, label, start_index) = scope_stack.pop().unwrap();
                    let block = self.scope_statements.drain(start_index..).collect();

                    let condition = scope.condition.map(|condition| {
                        let transition = &nodes[condition.condition].transition;
                        let converted_transition: Expression =
                            self.convert_transition(kind, transition, items, cx);

                        let mut expr = Box::new(converted_transition);
                        if condition.negate {
                            expr = Box::new(Expression::Unary {
                                op: UnaryOp::Negate,
                                expr,
                            })
                        }

                        expr
                    });

                    let block_expression = match (scope.kind, condition) {
                        (ScopeKind::Block, Some(condition)) => {
                            let body = match label {
                                Some(_) => Block::new(Expression::Block(label, block)),
                                None => block,
                            };

                            Expression::If {
                                condition,
                                pass: body,
                                fail: None,
                            }
                        }
                        (ScopeKind::Block, None) => Expression::Block(label, block),
                        (ScopeKind::Loop, Some(condition)) => Expression::While {
                            label,
                            condition,
                            block,
                        },
                        (ScopeKind::Loop, None) => Expression::Loop(label, block),
                    };

                    self.scope_statements.push(block_expression);
                }
            }
        }

        assert!(scope_stack.is_empty());
        assert_eq!(self.scope_statements.len(), 1);

        let body = self.scope_statements.pop().unwrap();
        FunctionBody {
            variables: self.variables.take(),
            expr: body,
        }
    }
    fn convert_transition(
        &mut self,
        kind: RuleKind,
        transition: &Transition,
        items: &InitialItems,
        cx: &CodeFileCx,
    ) -> Expression {
        match transition {
            Transition::Error => Expression::Error,
            Transition::ByteSet(bytes) => Expression::Call {
                handle: items.lexer_set,
                arguments: vec![
                    Expression::AccessArgument(0),
                    Value::Bytes(bytes.clone()).into(),
                ],
            },
            Transition::Bytes(bytes) => Expression::Call {
                handle: items.lexer_bytes,
                arguments: vec![
                    Expression::AccessArgument(0),
                    Value::Bytes(bytes.clone()).into(),
                ],
            },
            Transition::Keyword(bytes) => Expression::Call {
                handle: items.lexer_keyword,
                arguments: vec![
                    Expression::AccessArgument(0),
                    Value::Bytes(bytes.clone()).into(),
                ],
            },
            &Transition::Rule(handle) => {
                let args = [Expression::AccessArgument(0), Value::U32(0).into()];
                let args = match self.is_pratt_rule.contains(handle) {
                    true => &args[..],
                    false => &args[..1],
                };
                Expression::Call {
                    handle: self.function_handles[handle],
                    arguments: args.to_owned(),
                }
            }
            &Transition::PrattRule(pratt_rule, min_bp) => {
                assert!(self.is_pratt_rule.contains(pratt_rule));
                Expression::Call {
                    handle: self.function_handles[pratt_rule],
                    arguments: vec![Expression::AccessArgument(0), Value::U32(min_bp).into()],
                }
            }
            &Transition::CompareBindingPower(bp) => {
                let own_bp = Value::U32(bp).into();
                let min_bp = Expression::AccessArgument(1);
                Expression::Binary {
                    op: BinaryOp::Less,
                    left: Box::new(min_bp),
                    right: Box::new(own_bp),
                }
            }
            Transition::Any => Expression::Call {
                handle: items.lexer_any,
                arguments: vec![Expression::AccessArgument(0)],
            },
            &Transition::Not(a) => Expression::Call {
                handle: items.lexer_not,
                arguments: vec![
                    Expression::AccessArgument(0),
                    Expression::Value(Value::EnumVariant(
                        items.tree_kind,
                        cx.rule_to_tree_kind_value[a],
                    )),
                ],
            },
            &Transition::SaveState(variable) => {
                let function = match kind {
                    RuleKind::Tokens => items.lexer_save_position,
                    RuleKind::Rules => items.parser_save_position,
                };
                let position = match kind {
                    RuleKind::Tokens => items.lexer_position,
                    RuleKind::Rules => items.parser_position,
                };
                let handle = self.add_variable(variable, "checkpoint", position.as_type());

                Expression::DeclareVariable {
                    handle,
                    value: Some(Box::new(Expression::Call {
                        handle: function,
                        arguments: vec![Expression::AccessArgument(0)],
                    })),
                }
            }
            &Transition::RestoreState(variable) => {
                let compact = self.get_variable(variable);
                let function = match kind {
                    RuleKind::Tokens => items.lexer_restore_position,
                    RuleKind::Rules => items.parser_restore_position,
                };

                Expression::Call {
                    handle: function,
                    arguments: vec![
                        Expression::AccessArgument(0),
                        Expression::AccessVariable(compact),
                    ],
                }
            }
            &Transition::CloseSpan(rule) => {
                let function = match kind {
                    RuleKind::Tokens => items.lexer_close_span,
                    RuleKind::Rules => items.parser_close_span,
                };

                Expression::Call {
                    handle: function,
                    arguments: vec![
                        Expression::AccessArgument(0),
                        Value::EnumVariant(items.tree_kind, cx.rule_to_tree_kind_value[rule])
                            .into(),
                    ],
                }
            }
            &Transition::Return(a) => Expression::Return(Some(Box::new(Value::Bool(a).into()))),
            &Transition::Dummy(a) => Value::Bool(a).into(),
        }
    }
}
