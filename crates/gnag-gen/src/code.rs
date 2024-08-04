use gnag::{
    ast::RuleKind,
    ctx::ErrorAccumulator,
    handle::{HandleBitset, HandleVec, SecondaryVec, TypedHandle},
    simple_handle, StrSpan,
};

use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    compile::CompiledFile,
    convert::{ConvertedFile, RuleDef, RuleHandle},
    expr::{self, RuleExpr, Transition, TransitionEffects},
    scope_tree::{ScopeKind, ScopeNodeHandle},
    structure::{mark_used_labels, FlowAction, GraphStructuring, Statement},
};

simple_handle! {
    pub FunctionHandle,
    pub StructHandle,
    pub EnumHandle,
    pub ForeignTypeHandle,
    pub ConstantHandle,
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
        Type::Item(ItemHandle::Struct(self))
    }
}

impl EnumHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.enums[self].name
    }
    pub fn as_type(self) -> Type {
        Type::Item(ItemHandle::Enum(self))
    }
}

impl ForeignTypeHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.foreign_types[self].name
    }
    pub fn as_type(self) -> Type {
        Type::Item(ItemHandle::Foreign(self))
    }
}

impl ConstantHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        &module.constants[self].name
    }
    pub fn as_type(self) -> Type {
        Type::Item(ItemHandle::Constant(self))
    }
}

pub struct ForeignItems {
    pub lexer: ForeignTypeHandle,
    pub parser: ForeignTypeHandle,

    pub language_nodes: StructHandle,
    pub language: StructHandle,

    pub span_start: ForeignTypeHandle,
    pub lexer_position: ForeignTypeHandle,
    pub parser_position: ForeignTypeHandle,

    pub node_event: ForeignTypeHandle,
    pub node_kind: ForeignTypeHandle,
    pub node_kind_new: FunctionHandle,

    pub lexer_save_position: FunctionHandle,
    pub lexer_restore_position: FunctionHandle,
    pub lexer_finish_token: FunctionHandle,

    pub lexer_bytes: FunctionHandle,
    pub lexer_set: FunctionHandle,
    pub lexer_keyword: FunctionHandle,
    pub lexer_any: FunctionHandle,
    pub lexer_not: FunctionHandle,

    pub parser_save_position: FunctionHandle,
    pub parser_restore_position: FunctionHandle,
    pub parser_open_span: FunctionHandle,
    pub parser_close_span: FunctionHandle,

    pub parser_token: FunctionHandle,
    pub parser_any: FunctionHandle,
    pub parser_not: FunctionHandle,
}

impl ForeignItems {
    pub fn register(module: &mut CodeFile) -> ForeignItems {
        let lexer = module.register_foreign_type("Lexer");
        let parser = module.register_foreign_type("Parser");

        let lexer_ref = lexer.as_type().clone().to_ref();
        let lexer_mut = lexer.as_type().clone().to_ref_mut();
        let parser_ref = parser.as_type().clone().to_ref();
        let parser_mut = parser.as_type().clone().to_ref_mut();

        let language_nodes = module.register_struct(
            "LanguageNodes",
            &[
                ("skip_bound", &Type::U16),
                ("token_bound", &Type::U16),
                ("total_bound", &Type::U16),
                (
                    "names",
                    &Type::Str.to_static_ref().to_slice().to_static_ref(),
                ),
            ],
        );
        let language = module.register_struct(
            "Language",
            &[
                (
                    "lexer_entry",
                    &Type::FunctionPointer(std::slice::from_ref(&lexer_mut).into()),
                ),
                (
                    "parser_entry",
                    &Type::FunctionPointer(std::slice::from_ref(&parser_mut).into()),
                ),
                ("nodes", &language_nodes.as_type()),
            ],
        );

        let span_start = module.register_foreign_type("SpanStart");
        let lexer_position = module.register_foreign_type("LexerPosition");
        let parser_position = module.register_foreign_type("ParserPosition");

        let node_event = module.register_foreign_type("NodeEvent");
        let node_kind = module.register_foreign_type("NodeKind");
        let node_kind_new =
            module.declare_function("NodeKind::new", &[("raw", &Type::U16)], node_kind);

        let lexer_arg = ("self", &lexer_ref);
        let lexer_mut_arg = ("self", &lexer_mut);
        let parser_arg = ("self", &parser_ref);
        let parser_mut_arg = ("self", &parser_mut);
        let span_start_arg = ("start", &span_start.as_type());
        let lexer_position_arg = ("position", &lexer_position.as_type());
        let parser_position_arg = ("position", &parser_position.as_type());
        let token_arg = ("kind", &node_kind.as_type());

        let bytes_arg = ("bytes", &Type::U8.to_slice().to_ref());

        ForeignItems {
            node_event,
            node_kind,
            node_kind_new,
            language,
            language_nodes,

            lexer_save_position: module.declare_function(
                "save_position",
                &[lexer_arg],
                lexer_position,
            ),
            lexer_restore_position: module.declare_function(
                "restore_position",
                &[lexer_mut_arg, lexer_position_arg],
                Type::Unit,
            ),
            lexer_finish_token: module.declare_function(
                "finish_token",
                &[lexer_mut_arg, token_arg],
                span_start.as_type(),
            ),

            lexer_bytes: module.declare_function("bytes", &[lexer_mut_arg, bytes_arg], Type::Bool),
            lexer_set: module.declare_function("set", &[lexer_mut_arg, bytes_arg], Type::Bool),
            lexer_keyword: module.declare_function(
                "keyword",
                &[lexer_mut_arg, bytes_arg],
                Type::Bool,
            ),
            lexer_any: module.declare_function("any", &[lexer_mut_arg], Type::Bool),
            lexer_not: module.declare_function("not", &[lexer_mut_arg], Type::Bool),

            parser_save_position: module.declare_function(
                "save_position",
                &[parser_arg],
                parser_position,
            ),
            parser_restore_position: module.declare_function(
                "restore_position",
                &[parser_mut_arg, parser_position_arg],
                Type::Unit,
            ),
            parser_open_span: module.declare_function(
                "open_span",
                &[parser_mut_arg],
                span_start.as_type(),
            ),
            parser_close_span: module.declare_function(
                "close_span",
                &[parser_mut_arg, span_start_arg],
                Type::Unit,
            ),
            parser_token: module.declare_function(
                "token",
                &[parser_mut_arg, token_arg],
                Type::Bool,
            ),
            parser_any: module.declare_function("any", &[parser_mut_arg], Type::Bool),
            parser_not: module.declare_function("not", &[parser_mut_arg, token_arg], Type::Bool),

            lexer,
            parser,
            span_start,
            lexer_position,
            parser_position,
        }
    }

    pub fn rule_class_type(&self, kind: RuleKind) -> Type {
        match kind {
            RuleKind::Tokens => self.lexer.as_type(),
            RuleKind::Rules => self.parser.as_type(),
        }
    }
}

pub struct CodeFileCx<'a, 'b, 'c> {
    pub err: &'a ErrorAccumulator,
    pub converted: &'b ConvertedFile,
    pub compiled: &'c CompiledFile,
}

impl<'a, 'b, 'c> CodeFileCx<'a, 'b, 'c> {
    pub fn new(
        err: &'a ErrorAccumulator,
        converted: &'b ConvertedFile,
        compiled: &'c CompiledFile,
    ) -> CodeFileCx<'a, 'b, 'c> {
        Self {
            err,
            converted,
            compiled,
        }
    }
}

#[derive(Default)]
pub struct CodeFile {
    pub functions: HandleVec<FunctionHandle, Function>,
    pub structs: HandleVec<StructHandle, Struct>,
    pub enums: HandleVec<EnumHandle, Enum>,
    pub foreign_types: HandleVec<ForeignTypeHandle, ForeignType>,
    pub constants: HandleVec<ConstantHandle, Constant>,

    pub supressed_items: HashSet<ItemHandle>,
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

        let items = ForeignItems::register(&mut this);

        let cx = CodeFileCx::new(err, converted, compiled);
        GeneratedItems::register(&mut this, &items, &cx);

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
    pub fn function_add_body(&mut self, function: FunctionHandle, body: FunctionBody) {
        let fun = &mut self.functions[function];
        assert!(fun.body.is_none());
        fun.body = Some(body);
    }
    pub fn register_struct(
        &mut self,
        name: impl Into<String>,
        fields: &[(&str, &Type)],
    ) -> StructHandle {
        let fields = fields
            .into_iter()
            .copied()
            .map(|(a, b)| (a.to_string(), b.clone()))
            .collect();

        self.structs.push(Struct {
            name: name.into(),
            fields,
        })
    }
    pub fn register_foreign_type(&mut self, name: impl Into<String>) -> ForeignTypeHandle {
        self.foreign_types.push(ForeignType { name: name.into() })
    }
    pub fn register_constant(
        &mut self,
        name: impl Into<String>,
        type_: impl Into<Type>,
        value: Expression,
    ) -> ConstantHandle {
        self.constants.push(Constant {
            name: name.into(),
            type_: type_.into(),
            value,
        })
    }
    pub fn supress_item(&mut self, item: ItemHandle) {
        self.supressed_items.insert(item);
    }

    #[allow(unused_must_use)]
    pub fn display(&self, buf: &mut dyn std::fmt::Write) {
        for (handle, body) in self.foreign_types.iter_kv() {
            if self.supressed_items.contains(&ItemHandle::from(handle)) {
                continue;
            }

            let name = &body.name;
            writeln!(buf, "/// extern type {name}");
        }

        for (_, constant) in self.constants.iter_kv() {
            let name = &constant.name;
            write!(buf, "pub const {name}: ");
            constant.type_.display(buf, self);
            write!(buf, " = ");
            constant.value.display(buf, self, None);
            write!(buf, ";\n");
        }

        for (handle, function) in self.functions.iter_kv() {
            if self.supressed_items.contains(&ItemHandle::from(handle)) {
                continue;
            }

            if function.body.is_none() {
                write!(buf, "/// extern ");
                self.display_function(buf, function);
                write!(buf, "\n");
            }
        }

        for (handle, body) in self.structs.iter_kv() {
            if self.supressed_items.contains(&ItemHandle::from(handle)) {
                continue;
            }

            let name = &body.name;
            write!(buf, "pub struct {name} {{\n");
            for (name, _type) in &body.fields {
                write!(buf, "    {name}: ");
                _type.display(buf, self);
                write!(buf, ",\n");
            }
            write!(buf, "}}\n");
        }

        for (handle, body) in self.enums.iter_kv() {
            if self.supressed_items.contains(&ItemHandle::from(handle)) {
                continue;
            }

            let name = &body.name;
            write!(buf, "pub enum {name} {{\n",);
            for (name, value) in &body.variants {
                write!(buf, "    {name} = {value},\n");
            }
            write!(buf, "}}\n");
        }

        for (handle, function) in self.functions.iter_kv() {
            if self.supressed_items.contains(&ItemHandle::from(handle)) {
                continue;
            }

            if let Some(body) = &function.body {
                write!(buf, "pub ");
                self.display_function(buf, function);
                let is_block = matches!(body.expr, Expression::Block(..));
                if !is_block {
                    write!(buf, " {{\n");
                }
                body.expr.display(buf, self, Some(function));
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ItemHandle {
    Struct(StructHandle),
    Enum(EnumHandle),
    Foreign(ForeignTypeHandle),
    Constant(ConstantHandle),
    Function(FunctionHandle),
}

impl From<StructHandle> for ItemHandle {
    fn from(value: StructHandle) -> Self {
        Self::Struct(value)
    }
}
impl From<EnumHandle> for ItemHandle {
    fn from(value: EnumHandle) -> Self {
        Self::Enum(value)
    }
}
impl From<ForeignTypeHandle> for ItemHandle {
    fn from(value: ForeignTypeHandle) -> Self {
        Self::Foreign(value)
    }
}
impl From<ConstantHandle> for ItemHandle {
    fn from(value: ConstantHandle) -> Self {
        Self::Constant(value)
    }
}

impl From<FunctionHandle> for ItemHandle {
    fn from(value: FunctionHandle) -> Self {
        Self::Function(value)
    }
}

impl ItemHandle {
    pub fn name(self, module: &CodeFile) -> &str {
        match self {
            ItemHandle::Struct(a) => a.name(module),
            ItemHandle::Enum(a) => a.name(module),
            ItemHandle::Foreign(a) => a.name(module),
            ItemHandle::Constant(a) => a.name(module),
            ItemHandle::Function(a) => a.name(module),
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
    Str,
    Unit,
    Item(ItemHandle),
    StaticRef(Box<Type>),
    Ref(Box<Type>),
    RefMut(Box<Type>),
    FunctionPointer(Box<[Type]>),
    Slice(Box<Type>),
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
            Type::Str => "str",
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
            Type::FunctionPointer(args) => {
                write!(buf, "fn(");
                let mut first = true;
                for arg in args.iter() {
                    if !first {
                        write!(buf, ", ");
                    }
                    first = true;
                    arg.display(buf, module);
                }
                write!(buf, ")");
                return;
            }
            Type::StaticRef(inner) => {
                write!(buf, "&'static ");
                inner.display(buf, module);
                return;
            }
            Type::Slice(inner) => {
                write!(buf, "[");
                inner.display(buf, module);
                write!(buf, "]");
                return;
            }
        };
        write!(buf, "{name}");
    }
    pub fn to_ref(self) -> Type {
        Type::Ref(Box::new(self))
    }
    pub fn to_static_ref(self) -> Type {
        Type::StaticRef(Box::new(self))
    }
    pub fn to_ref_mut(self) -> Type {
        Type::RefMut(Box::new(self))
    }
    pub fn to_slice(self) -> Type {
        Type::Slice(Box::new(self))
    }
}

// implement From directly, rather than relying on Handle->ItemType->Type
// which cannot be inferred
impl From<StructHandle> for Type {
    fn from(value: StructHandle) -> Self {
        Type::Item(ItemHandle::Struct(value))
    }
}

impl From<EnumHandle> for Type {
    fn from(value: EnumHandle) -> Self {
        Type::Item(ItemHandle::Enum(value))
    }
}

impl From<ForeignTypeHandle> for Type {
    fn from(value: ForeignTypeHandle) -> Self {
        Type::Item(ItemHandle::Foreign(value))
    }
}

impl From<ItemHandle> for Type {
    fn from(value: ItemHandle) -> Self {
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
    Str(Rc<str>),
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
            Value::Str(a) => {
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
    Ref,
    RefMut,
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
    Constant(ConstantHandle),
    FunctionPointer(FunctionHandle),
    RecordLiteral {
        type_: ItemHandle,
        fields: Vec<Expression>,
    },
    ArrayLiteral(Vec<Expression>),
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
        function: Option<&Function>,
    ) {
        fn display_block(
            label: Option<BlockLabel>,
            block: &Block,
            keyword: Option<&str>,
            condition: Option<&Expression>,
            buf: &mut dyn std::fmt::Write,
            // cx: &CodeFileCx,
            module: &CodeFile,
            function: Option<&Function>,
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
                if !matches!(
                    a,
                    Expression::Block(..)
                        | Expression::Loop(..)
                        | Expression::While { .. }
                        | Expression::If { .. }
                ) {
                    write!(buf, ";");
                }
                write!(buf, "\n");
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

        fn display_in_parens(
            expr: &Expression,
            buf: &mut dyn std::fmt::Write,
            module: &CodeFile,
            function: Option<&Function>,
        ) {
            let need_parens = matches!(expr, Expression::Binary { .. } | Expression::Unary { .. });
            if need_parens {
                write!(buf, "(");
            }
            expr.display(buf, module, function);
            if need_parens {
                write!(buf, ")");
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
                let mut arguments = arguments.as_slice();

                let definition_arguments = module.functions[*handle].arguments.as_slice();
                if definition_arguments
                    .first()
                    .map_or(false, |(name, _)| name == "self")
                {
                    display_in_parens(&arguments[0], buf, module, function);
                    write!(buf, ".");
                    arguments = &arguments[1..];
                }

                let name = handle.name(module);
                write!(buf, "{name}(");
                let mut first = true;
                for a in arguments {
                    if !first {
                        write!(buf, ", ");
                    }
                    first = false;
                    a.display(buf, module, function);
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
                display_in_parens(left, buf, module, function);
                write!(buf, " {op} ");
                display_in_parens(right, buf, module, function);
            }
            Expression::Unary { op, expr } => {
                let op = match op {
                    UnaryOp::Negate => "!",
                    UnaryOp::Ref => "&",
                    UnaryOp::RefMut => "&mut ",
                };
                write!(buf, "{op}");
                display_in_parens(expr, buf, module, function);
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
                let (name, type_) = function.unwrap().get_variable(*handle);

                write!(buf, "let {name}: ");
                type_.display(buf, module);

                if let Some(value) = value {
                    write!(buf, " = ");
                    value.display(buf, module, function);
                }
            }
            Expression::StoreVariable(handle, value) => {
                let (name, _) = function.unwrap().get_variable(*handle);
                write!(buf, "let {name} = ");
                value.display(buf, module, function);
            }
            Expression::AccessVariable(handle) => {
                let (name, _) = function.unwrap().get_variable(*handle);
                write!(buf, "{name}");
            }
            Expression::AccessArgument(index) => {
                let (name, _) = function.unwrap().get_argument(*index);
                write!(buf, "{name}");
            }
            Expression::FunctionPointer(handle) => {
                let name = handle.name(module);
                write!(buf, "{name}");
            }
            Expression::RecordLiteral { type_, fields } => {
                let ItemHandle::Struct(handle) = *type_ else {
                    panic!("Expected struct");
                };

                let name = handle.name(module);
                let body = &module.structs[handle];

                assert!(body.fields.len() == fields.len());

                write!(buf, "{name} {{\n");
                for ((name, _), value) in body.fields.iter().zip(fields) {
                    write!(buf, "  {name}: ");
                    value.display(buf, module, function);
                    write!(buf, ",\n");
                }
                write!(buf, "}}");
            }
            Expression::Constant(handle) => {
                let name = handle.name(module);
                write!(buf, "{name}");
            }
            Expression::ArrayLiteral(elements) => {
                write!(buf, "[\n");
                for expr in elements {
                    expr.display(buf, module, function);
                    write!(buf, ",\n");
                }
                write!(buf, "]");
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

impl Function {
    pub fn get_argument(&self, index: u32) -> (&str, &Type) {
        let (name, ty) = &self.arguments[index as usize];
        (name.as_str(), ty)
    }
    pub fn get_variable(&self, handle: VariableHandle) -> (&str, &Type) {
        let (name, ty) = &self.body.as_ref().unwrap().variables[handle];
        (name.as_str(), ty)
    }
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

pub struct Constant {
    pub name: String,
    pub type_: Type,
    pub value: Expression,
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

struct GeneratedItems {
    #[allow(unused)]
    language_entrypoint: ConstantHandle,
    is_pratt_rule: HandleBitset<RuleHandle>,
    rule_to_function: SecondaryVec<RuleHandle, FunctionHandle>,
    rule_to_tree_kind_value: HandleVec<RuleHandle, ConstantHandle>,
}

impl RuleBuilder {
    pub fn clear(&mut self) {
        self.variables.clear();
        self.sparse_variables.clear();
        self.compact_scopes.clear();
        self.scope_statements.clear();
    }
}

impl GeneratedItems {
    fn register(module: &mut CodeFile, items: &ForeignItems, cx: &CodeFileCx) {
        let this = GeneratedItems::new(items, module, cx);
        let mut builder = RuleBuilder::default();

        for (handle, &reserved) in this.rule_to_function.iter_kv() {
            let body = builder.convert_rule(handle, items, &this, cx);
            module.function_add_body(reserved, body);
        }
    }
    fn new(items: &ForeignItems, module: &mut CodeFile, cx: &CodeFileCx) -> GeneratedItems {
        let is_pratt_rule = Self::make_is_pratt(cx.converted);

        let rule_to_function = Self::declare_functions(&is_pratt_rule, items, module, cx);

        let (language_entrypoint, rule_to_tree_kind_value) =
            Self::make_node_kind_constants(&rule_to_function, items, module, cx);

        Self {
            rule_to_function,
            is_pratt_rule,
            rule_to_tree_kind_value,
            language_entrypoint,
        }
    }
    fn make_node_kind_constants(
        rule_to_function: &SecondaryVec<RuleHandle, FunctionHandle>,
        items: &ForeignItems,
        module: &mut CodeFile,
        cx: &CodeFileCx,
    ) -> (ConstantHandle, HandleVec<RuleHandle, ConstantHandle>) {
        let mut rules = Vec::with_capacity(cx.converted.rules.len());

        let add_filter = |rules: &mut Vec<RuleHandle>, filter: fn(&RuleDef) -> bool| -> u16 {
            rules.extend(cx.converted.rules.iter_kv().filter_map(|(handle, rule)| {
                match filter(rule) {
                    true => Some(handle),
                    false => None,
                }
            }));

            rules.len().try_into().unwrap()
        };

        let skip_bound = add_filter(&mut rules, |rule| {
            return rule.kind == RuleKind::Tokens && rule.body.attributes.skip;
        });

        let token_bound = add_filter(&mut rules, |rule| {
            return rule.kind == RuleKind::Tokens && !rule.body.attributes.skip;
        });

        let total_bound = add_filter(&mut rules, |rule| {
            return rule.kind == RuleKind::Rules;
        });

        let mut collected_rules = SecondaryVec::with_capacity(cx.converted.rules.len());
        for (index, handle) in rules.iter().copied().enumerate() {
            let name = handle.name(cx.converted);
            // NodeKind must be nonzero so we add 1
            let value: u16 = (index + 1).try_into().unwrap();

            let constant = module.register_constant(
                name,
                items.node_kind,
                Expression::Call {
                    handle: items.node_kind_new,
                    arguments: vec![Value::U16(value).into()],
                },
            );

            collected_rules.insert(handle, constant);
        }

        let rule_to_constant = collected_rules.try_into().unwrap();

        // the Language constant with function pointers to lexer and parser entrypoints
        let language = {
            let root_rule = cx
                .converted
                .rules
                .iter_kv()
                .find(|(_, rule)| rule.body.attributes.root);

            let parser_function = root_rule
                .map(|(handle, _)| Expression::FunctionPointer(rule_to_function[handle]))
                .unwrap_or_else(|| {
                    cx.err.error(StrSpan::empty(), "No @root rule");
                    Expression::Error
                });

            let lexer_function = cx
                .converted
                .lexer
                .map(|handle| Expression::FunctionPointer(rule_to_function[handle]))
                .unwrap_or_else(|| {
                    cx.err.error(StrSpan::empty(), "No tokens");
                    Expression::Error
                });

            // the actual kinds start at 1 because they are using NonZeroU16
            let mut names = vec![Value::Str("NONE".into()).into()];
            names.extend(
                rules
                    .iter()
                    .map(|handle| Value::Str(handle.name(cx.converted).into()).into()),
            );

            let language_nodes = Expression::RecordLiteral {
                type_: items.language_nodes.into(),
                fields: vec![
                    Value::U16(skip_bound).into(),
                    Value::U16(token_bound).into(),
                    Value::U16(total_bound).into(),
                    Expression::Unary {
                        op: UnaryOp::Ref,
                        expr: Box::new(Expression::ArrayLiteral(names)),
                    },
                ],
            };

            module.register_constant(
                "LANGUAGE",
                items.language,
                Expression::RecordLiteral {
                    type_: items.language.into(),
                    fields: vec![lexer_function, parser_function, language_nodes],
                },
            )
        };

        (language, rule_to_constant)
    }
    fn declare_functions(
        is_pratt_rule: &HandleBitset<RuleHandle>,
        items: &ForeignItems,
        module: &mut CodeFile,
        cx: &CodeFileCx,
    ) -> SecondaryVec<RuleHandle, FunctionHandle> {
        let lexer = items.lexer.as_type().to_ref_mut();
        let parser = items.parser.as_type().to_ref_mut();

        let lexer_arg = ("l", &lexer);
        let parser_arg = ("p", &parser);

        cx.converted
            .rules
            .map_ref_with_key(|handle, rule| {
                if (rule.kind == RuleKind::Tokens && rule.is_toplevel)
                    || (rule.kind == RuleKind::Rules && !rule.is_toplevel)
                {
                    return None;
                }

                let object = match rule.kind {
                    RuleKind::Tokens => lexer_arg,
                    RuleKind::Rules => parser_arg,
                };

                let args = [object, ("min_bp", &Type::U32)];
                let args = match is_pratt_rule.contains(handle) {
                    true => &args[..],
                    false => &args[..1],
                };

                let function_handle =
                    module.declare_function(rule.body.name.clone(), args, Type::Bool);
                Some(function_handle)
            })
            .into()
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
}

#[derive(Default)]
struct RuleBuilder {
    variables: HandleVec<VariableHandle, (String, Type)>,
    sparse_variables: HashMap<expr::VariableHandle, VariableHandle>,
    compact_scopes: RemapHandles,
    scope_statements: Vec<Expression>,
}

impl RuleBuilder {
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
        items: &ForeignItems,
        generated: &GeneratedItems,
        cx: &CodeFileCx,
    ) -> FunctionBody {
        self.clear();

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

                    let convert_action =
                        |builder: &RuleBuilder, action: FlowAction| -> Option<Expression> {
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
                        self.convert_transition(kind, transition, items, generated, cx);

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
                            self.convert_transition(kind, transition, items, generated, cx);

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
        parent_kind: RuleKind,
        transition: &Transition,
        items: &ForeignItems,
        generated: &GeneratedItems,
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
                let kind = cx.converted.rules[handle].kind;
                if parent_kind == RuleKind::Rules && kind == RuleKind::Tokens {
                    Expression::Call {
                        handle: items.parser_token,
                        arguments: vec![
                            Expression::AccessArgument(0),
                            Expression::Constant(generated.rule_to_tree_kind_value[handle]),
                        ],
                    }
                } else {
                    let args = [Expression::AccessArgument(0), Value::U32(0).into()];
                    let args = match generated.is_pratt_rule.contains(handle) {
                        true => &args[..],
                        false => &args[..1],
                    };
                    Expression::Call {
                        handle: generated.rule_to_function[handle],
                        arguments: args.to_owned(),
                    }
                }
            }
            &Transition::PrattRule(pratt_rule, min_bp) => {
                assert!(generated.is_pratt_rule.contains(pratt_rule));
                Expression::Call {
                    handle: generated.rule_to_function[pratt_rule],
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
            &Transition::Not(rule) => Expression::Call {
                handle: items.lexer_not,
                arguments: vec![
                    Expression::AccessArgument(0),
                    Expression::Constant(generated.rule_to_tree_kind_value[rule]),
                ],
            },
            &Transition::SaveState(variable) => {
                let function = match parent_kind {
                    RuleKind::Tokens => items.lexer_save_position,
                    RuleKind::Rules => items.parser_save_position,
                };
                let position = match parent_kind {
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
                let function = match parent_kind {
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
                let function = match parent_kind {
                    RuleKind::Tokens => items.lexer_finish_token,
                    RuleKind::Rules => items.parser_close_span,
                };

                Expression::Call {
                    handle: function,
                    arguments: vec![
                        Expression::AccessArgument(0),
                        Expression::Constant(generated.rule_to_tree_kind_value[rule]),
                    ],
                }
            }
            &Transition::Return(a) => Expression::Return(Some(Box::new(Value::Bool(a).into()))),
            &Transition::Dummy(a) => Value::Bool(a).into(),
        }
    }
}
