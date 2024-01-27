use std::{
    cell::Cell,
    collections::HashMap,
    fmt::{Debug, Display, Write},
};

use gnag::{
    handle::{HandleCounter, HandleVec, SecondaryVec, TypedHandle},
    simple_handle, SpannedError, StrSpan,
};

use crate::{
    compile::{CompiledFile, CompiledRule},
    convert::{ConvertedFile, RuleExpr, RuleHandle},
    lower::LoweredFile,
    pratt::{PrattChild, PrattExpr, PrattExprKind},
};

simple_handle!(
    pub VariableHandle,
    pub FunctionHandle,
    pub BlockHandle,
    pub CustomTypeHandle
);

#[derive(Clone, Debug)]
pub enum FunctionBody {
    Builtin,
    Todo,
    Known(Expr),
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub args: Vec<ExprType>,
    pub ret: ExprType,
    pub body: FunctionBody,
}

impl Function {
    pub fn builtin(name: &str, args: &[ExprType], ret: ExprType) -> Function {
        Function {
            name: name.to_owned(),
            args: args.to_vec(),
            ret,
            body: FunctionBody::Builtin,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExprType {
    Never,
    Void,
    Bool,
    U32,
    String,
    SpanKind,
    Custom(CustomTypeHandle),
}

impl ExprType {
    fn get_name(self, module: &ModuleBuilder) -> &str {
        match self {
            ExprType::Never => "!",
            ExprType::Void => "()",
            ExprType::Bool => "bool",
            ExprType::U32 => "u32",
            ExprType::String => "String",
            ExprType::SpanKind => "u32",
            ExprType::Custom(a) => &module.custom_types[a],
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExprConstant {
    Void,
    Bool(bool),
    U32(u32),
    SpanKind(u32),
    String(String),
}

impl ExprConstant {
    pub fn ty(&self) -> ExprType {
        match self {
            ExprConstant::Void => ExprType::Void,
            ExprConstant::Bool(_) => ExprType::Bool,
            ExprConstant::U32(_) => ExprType::U32,
            ExprConstant::SpanKind(_) => ExprType::SpanKind,
            ExprConstant::String(_) => ExprType::String,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    Error,
    Empty,
    Negate(Box<Expr>),
    LessOrEqual(Box<Expr>, Box<Expr>),
    MoreOrEqual(Box<Expr>, Box<Expr>),
    Less(Box<Expr>, Box<Expr>),
    More(Box<Expr>, Box<Expr>),
    Equal(Box<Expr>, Box<Expr>),
    NotEqual(Box<Expr>, Box<Expr>),
    VariableAccess(VariableHandle),
    DeclareVariable {
        handle: VariableHandle,
        mutable: bool,
        value: Option<Box<Expr>>,
    },
    AssignVariable {
        handle: VariableHandle,
        value: Box<Expr>,
    },
    Constant(ExprConstant),
    Call {
        fun: FunctionHandle,
        arguments: Vec<Expr>,
    },
    If {
        condition: Box<Expr>,
        pass: Box<Expr>,
        otherwise: Option<Box<Expr>>,
    },
    While {
        condition: Box<Expr>,
        block: Box<Expr>,
    },
    Loop(Box<Expr>),
    Block {
        handle: BlockHandle,
        statements: Vec<Expr>,
    },
    Break(BlockHandle, Box<Expr>),
    Continue(BlockHandle),
}

pub struct ExprPrinter<'a, 'b> {
    module: &'a ModuleBuilder,
    writer: &'b mut dyn Write,
    indent: u32,
}

impl Write for ExprPrinter<'_, '_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        for c in s.chars() {
            self.writer.write_char(c)?;
            if c == '\n' {
                for _ in 0..self.indent {
                    self.writer.write_str("    ")?;
                }
            }
        }
        Ok(())
    }
}

impl<'a, 'b> ExprPrinter<'a, 'b> {
    pub fn new(module: &'a ModuleBuilder, writer: &'b mut dyn Write) -> ExprPrinter<'a, 'b> {
        Self {
            module,
            writer,
            indent: 0,
        }
    }
    pub fn push(&mut self) {
        self.indent += 1;
    }
    pub fn pop(&mut self) {
        self.indent = self.indent.checked_sub(1).unwrap();
    }
    fn fmt_monoop(&mut self, str: &str, a: &Expr) -> std::fmt::Result {
        let w = self;
        w.write_str(str)?;
        a.print(w)
    }
    fn fmt_binop(&mut self, a: &Expr, str: &str, b: &Expr) -> std::fmt::Result {
        let w = self;
        a.print(w)?;
        write!(w, " {str} ")?;
        b.print(w)
    }
    fn fmt_enclosed_delimited_generic<T>(
        &mut self,
        arguments: &[T],
        mut element: impl FnMut(&T, usize, &mut ExprPrinter) -> std::fmt::Result,
        start: &str,
        end: &str,
        delimiter: &str,
        multiline: bool,
    ) -> std::fmt::Result {
        let w = self;
        w.write_str(start)?;
        if !multiline {
            let mut first = true;
            for (i, a) in arguments.iter().enumerate() {
                if !first {
                    write!(w, "{delimiter} ")?;
                }
                first = false;
                element(a, i, w)?;
            }
        } else {
            w.push();
            for (i, a) in arguments.iter().enumerate() {
                write!(w, "\n")?;
                element(a, i, w)?;
                write!(w, "{delimiter}")?;
            }
            w.pop();
            write!(w, "\n")?;
        }
        w.write_str(end)
    }
    fn fmt_enclosed_delimited(
        &mut self,
        arguments: &[Expr],
        start: &str,
        end: &str,
        delimiter: &str,
        multiline: bool,
    ) -> std::fmt::Result {
        self.fmt_enclosed_delimited_generic(
            arguments,
            |a, _, w| a.print(w),
            start,
            end,
            delimiter,
            multiline,
        )
    }
    fn brace_delimited(&mut self, expr: &Expr) -> std::fmt::Result {
        let w = self;
        match expr {
            Expr::Empty { .. } => w.write_str("{ }"),
            Expr::Block { .. } => expr.print(w),
            _ => {
                w.push();
                write!(w, "{{\n")?;
                expr.print(w)?;
                w.pop();
                write!(w, "\n}}")
            }
        }
    }
}

impl Expr {
    pub fn print(&self, w: &mut ExprPrinter) -> Result<(), std::fmt::Error> {
        match self {
            Expr::Error => write!(w, "/* Parsing error */"),
            Expr::Empty => write!(w, "()"),
            Expr::Negate(a) => w.fmt_monoop("!", a),
            Expr::LessOrEqual(a, b) => w.fmt_binop(a, "<=", b),
            Expr::MoreOrEqual(a, b) => w.fmt_binop(a, ">=", b),
            Expr::Less(a, b) => w.fmt_binop(a, "<", b),
            Expr::More(a, b) => w.fmt_binop(a, ">", b),
            Expr::Equal(a, b) => w.fmt_binop(a, "==", b),
            Expr::NotEqual(a, b) => w.fmt_binop(a, "!=", b),
            Expr::VariableAccess(i) => write!(w, "v{}", i.index()),
            Expr::DeclareVariable {
                handle,
                mutable,
                value,
            } => {
                let m = match mutable {
                    true => " mut",
                    false => "",
                };
                write!(w, "let{m} v{}", handle.index())?;
                if let Some(a) = value {
                    write!(w, " = ")?;
                    a.print(w)?;
                }
                Ok(())
            }
            Expr::AssignVariable { handle, value } => {
                write!(w, "v{} = ", handle.index())?;
                value.print(w)
            }
            Expr::Constant(a) => match a {
                ExprConstant::Void => write!(w, "()"),
                ExprConstant::Bool(a) => write!(w, "{a}"),
                ExprConstant::U32(a) => write!(w, "{a}"),
                ExprConstant::SpanKind(a) => write!(w, "{a}"),
                ExprConstant::String(a) => write!(w, "{a:?}"),
            },
            Expr::Call { fun, arguments } => {
                let name = &w.module.functions[*fun].name;
                write!(w, "{name}")?;
                w.fmt_enclosed_delimited(arguments, "(", ")", ",", false)
            }
            Expr::If {
                condition,
                pass,
                otherwise,
            } => {
                write!(w, "if ")?;
                condition.print(w)?;
                write!(w, " ")?;
                w.brace_delimited(pass)?;
                if let Some(otherwise) = otherwise {
                    write!(w, " else ")?;
                    w.brace_delimited(&otherwise)?;
                }
                Ok(())
            }
            Expr::While { condition, block } => {
                write!(w, "while ")?;
                condition.print(w)?;
                write!(w, " ")?;
                w.brace_delimited(block)
            }
            Expr::Loop(a) => {
                write!(w, "loop ")?;
                w.brace_delimited(a)
            }
            Expr::Block { handle, statements } => {
                write!(w, "'b{}: {{", handle.index())?;

                if statements.is_empty() {
                    write!(w, " }}")
                } else {
                    w.push();
                    for a in statements {
                        write!(w, "\n")?;
                        a.print(w)?;
                        match a {
                            Expr::If { .. }
                            | Expr::While { .. }
                            | Expr::Loop(_)
                            | Expr::Block { .. } => {}
                            _ => write!(w, ";")?,
                        }
                    }
                    w.pop();
                    write!(w, "\n}}")
                }
            }
            Expr::Break(handle, b) => {
                write!(w, "break 'b{} ", handle.index())?;
                b.print(w)
            }
            Expr::Continue(handle) => {
                write!(w, "continue 'b{}", handle.index())
            }
        }
    }
}

#[allow(non_snake_case)]
pub mod expr {
    use super::{BlockHandle, Expr, ExprConstant, FunctionHandle, VariableHandle};
    pub fn Empty() -> Expr {
        Expr::Empty
    }
    pub fn Error() -> Expr {
        Expr::Error
    }
    pub fn Negate(expr: Expr) -> Expr {
        Expr::Negate(Box::new(expr))
    }
    pub fn LessOrEqual(left: Expr, right: Expr) -> Expr {
        Expr::LessOrEqual(Box::new(left), Box::new(right))
    }
    pub fn MoreOrEqual(left: Expr, right: Expr) -> Expr {
        Expr::MoreOrEqual(Box::new(left), Box::new(right))
    }
    pub fn Less(left: Expr, right: Expr) -> Expr {
        Expr::Less(Box::new(left), Box::new(right))
    }
    pub fn More(left: Expr, right: Expr) -> Expr {
        Expr::More(Box::new(left), Box::new(right))
    }
    pub fn Equal(left: Expr, right: Expr) -> Expr {
        Expr::Equal(Box::new(left), Box::new(right))
    }
    pub fn NotEqual(left: Expr, right: Expr) -> Expr {
        Expr::NotEqual(Box::new(left), Box::new(right))
    }
    pub fn Variable(variable: VariableHandle) -> Expr {
        Expr::VariableAccess(variable)
    }
    pub fn DeclareVar(variable: VariableHandle, mutable: bool, value: Option<Expr>) -> Expr {
        Expr::DeclareVariable {
            handle: variable,
            mutable,
            value: value.map(Box::new),
        }
    }
    pub fn AssignVar(variable: VariableHandle, value: Expr) -> Expr {
        Expr::AssignVariable {
            handle: variable,
            value: Box::new(value),
        }
    }
    pub fn Constant(constant: ExprConstant) -> Expr {
        Expr::Constant(constant)
    }
    pub fn Call(fun: FunctionHandle, arguments: Vec<Expr>) -> Expr {
        Expr::Call {
            fun,
            arguments: arguments,
        }
    }
    pub fn If(condition: Expr, pass: Expr) -> Expr {
        Expr::If {
            condition: Box::new(condition),
            pass: Box::new(pass),
            otherwise: None,
        }
    }
    pub fn IfElse(condition: Expr, pass: Expr, otherwise: Expr) -> Expr {
        Expr::If {
            condition: Box::new(condition),
            pass: Box::new(pass),
            otherwise: Some(Box::new(otherwise)),
        }
    }
    pub fn While(condition: Expr, block: Expr) -> Expr {
        Expr::While {
            condition: Box::new(condition),
            block: Box::new(block),
        }
    }
    pub fn Loop(expr: Expr) -> Expr {
        Expr::Loop(Box::new(expr))
    }
    pub fn Block(handle: BlockHandle, statements: Vec<Expr>) -> Expr {
        Expr::Block { handle, statements }
    }
    pub fn Break(block: BlockHandle, expr: Expr) -> Expr {
        Expr::Break(block, Box::new(expr))
    }
    pub fn Continue(block: BlockHandle) -> Expr {
        Expr::Continue(block)
    }

    pub fn Constant_bool(constant: bool) -> Expr {
        Expr::Constant(ExprConstant::Bool(constant))
    }
    pub fn Constant_u32(constant: u32) -> Expr {
        Expr::Constant(ExprConstant::U32(constant))
    }
    pub fn Constant_SpanKind(constant: u32) -> Expr {
        Expr::Constant(ExprConstant::SpanKind(constant))
    }
    pub fn Constant_String(constant: String) -> Expr {
        Expr::Constant(ExprConstant::String(constant))
    }
    pub fn Constant_str(constant: &str) -> Expr {
        Expr::Constant(ExprConstant::String(constant.to_owned()))
    }
}

pub struct SequenceBuilder {
    sequence: Vec<Expr>,
}

#[allow(non_snake_case)]
impl SequenceBuilder {
    pub fn new() -> SequenceBuilder {
        Self {
            sequence: Vec::new(),
        }
    }
    pub fn push(&mut self, expr: Expr) -> &mut SequenceBuilder {
        self.sequence.push(expr);
        self
    }
    pub fn Negate(&mut self, expr: Expr) -> &mut SequenceBuilder {
        self.sequence.push(expr::Negate(expr));
        self
    }
    pub fn Variable(&mut self, variable: VariableHandle) -> &mut SequenceBuilder {
        self.sequence.push(expr::Variable(variable));
        self
    }
    pub fn Constant(&mut self, constant: ExprConstant) -> &mut SequenceBuilder {
        self.sequence.push(expr::Constant(constant));
        self
    }
    pub fn Call(&mut self, fun: FunctionHandle, arguments: Vec<Expr>) -> &mut SequenceBuilder {
        self.sequence.push(expr::Call(fun, arguments));
        self
    }
    pub fn If(&mut self, condition: Expr, pass: Expr) -> &mut SequenceBuilder {
        self.sequence.push(expr::If(condition, pass));
        self
    }
    pub fn IfElse(&mut self, condition: Expr, pass: Expr, otherwise: Expr) -> &mut SequenceBuilder {
        self.sequence.push(expr::IfElse(condition, pass, otherwise));
        self
    }
    pub fn While(&mut self, condition: Expr, block: Expr) -> &mut SequenceBuilder {
        self.sequence.push(expr::While(condition, block));
        self
    }
    pub fn Loop(&mut self, expr: Expr) -> &mut SequenceBuilder {
        self.sequence.push(expr::Loop(expr));
        self
    }
    pub fn Block(&mut self, handle: BlockHandle, statements: Vec<Expr>) -> &mut SequenceBuilder {
        self.sequence.push(expr::Block(handle, statements));
        self
    }
    pub fn Break(&mut self, block: BlockHandle, expr: Expr) -> &mut SequenceBuilder {
        self.sequence.push(expr::Break(block, expr));
        self
    }
    pub fn Continue(&mut self, block: BlockHandle) -> &mut SequenceBuilder {
        self.sequence.push(expr::Continue(block));
        self
    }

    pub fn Constant_bool(&mut self, constant: bool) -> &mut SequenceBuilder {
        self.sequence.push(expr::Constant_bool(constant));
        self
    }
    pub fn Constant_u32(&mut self, constant: u32) -> &mut SequenceBuilder {
        self.sequence.push(expr::Constant_u32(constant));
        self
    }
    pub fn Constant_SpanKind(&mut self, constant: u32) -> &mut SequenceBuilder {
        self.sequence.push(expr::Constant_SpanKind(constant));
        self
    }
}

pub struct BlockBuilder<'a> {
    builder: &'a FunctionBuilder,
    handle: BlockHandle,
    statements: SequenceBuilder,
}

impl std::ops::Deref for BlockBuilder<'_> {
    type Target = SequenceBuilder;
    fn deref(&self) -> &Self::Target {
        &self.statements
    }
}
impl std::ops::DerefMut for BlockBuilder<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.statements
    }
}

impl<'a> BlockBuilder<'a> {
    pub fn new(builder: &'a FunctionBuilder) -> BlockBuilder<'a> {
        Self {
            builder,
            handle: builder.new_block(),
            statements: SequenceBuilder::new(),
        }
    }
    pub fn get_handle(&self) -> BlockHandle {
        self.handle
    }
    #[allow(non_snake_case)]
    pub fn DeclareVar(&mut self, mutable: bool, value: Option<Expr>) -> VariableHandle {
        let handle = self.builder.new_variable();
        self.sequence.push(expr::DeclareVar(handle, mutable, value));
        handle
    }
    #[allow(non_snake_case)]
    pub fn LetMut(&mut self, value: Expr) -> VariableHandle {
        self.DeclareVar(true, Some(value))
    }
    #[allow(non_snake_case)]
    pub fn Let(&mut self, value: Expr) -> VariableHandle {
        self.DeclareVar(false, Some(value))
    }
    #[allow(non_snake_case)]
    pub fn AssignVar(&mut self, variable: VariableHandle, value: Expr) -> &mut Self {
        self.sequence.push(expr::AssignVar(variable, value));
        self
    }
    #[allow(non_snake_case)]
    pub fn BreakSelf(&mut self, value: Expr) -> &mut Self {
        let block = self.get_handle();
        self.sequence.push(expr::Break(block, value));
        self
    }
    #[allow(non_snake_case)]
    pub fn IfBreakSelf(&mut self, condition: Expr, value: Expr) -> &mut Self {
        let block = self.get_handle();
        self.If(condition, expr::Break(block, value));
        self
    }
    pub fn finish(self) -> Expr {
        Expr::Block {
            handle: self.handle,
            statements: self.statements.sequence,
        }
    }
}

// pub struct CallBuilder {
//     handle: FunctionHandle,
//     statements: SequenceBuilder,
// }

// impl std::ops::Deref for CallBuilder {
//     type Target = SequenceBuilder;
//     fn deref(&self) -> &Self::Target {
//         &self.statements
//     }
// }
// impl std::ops::DerefMut for CallBuilder {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         &mut self.statements
//     }
// }

// impl CallBuilder {
//     pub fn new(function: FunctionHandle) -> CallBuilder {
//         Self {
//             handle: function,
//             statements: SequenceBuilder::new(),
//         }
//     }
//     pub fn finish(self) -> Expr {
//         Expr::Call {
//             fun: self.handle,
//             arguments: self.statements.sequence,
//         }
//     }
// }

#[derive(Debug)]
pub struct ModuleBuilder {
    pub custom_types: HandleVec<CustomTypeHandle, String>,
    pub functions: HandleVec<FunctionHandle, Function>,
}

impl ModuleBuilder {
    pub fn new() -> ModuleBuilder {
        Self {
            custom_types: HandleVec::new(),
            functions: HandleVec::new(),
        }
    }
    pub fn register_type(&mut self, name: &str) -> CustomTypeHandle {
        self.custom_types.push(name.to_owned())
    }
    pub fn builtin_fn(&mut self, name: &str, args: &[ExprType], ret: ExprType) -> FunctionHandle {
        self.functions.push(Function {
            name: name.to_owned(),
            args: args.to_vec(),
            ret,
            body: FunctionBody::Builtin,
        })
    }
    pub fn predeclare_fn(
        &mut self,
        name: &str,
        args: &[ExprType],
        ret: ExprType,
    ) -> FunctionHandle {
        self.functions.push(Function {
            name: name.to_owned(),
            args: args.to_vec(),
            ret,
            body: FunctionBody::Todo,
        })
    }
    pub fn finish_fn(&mut self, predeclared: FunctionHandle, body: Expr) {
        let fun = &mut self.functions[predeclared];
        assert!(matches!(fun.body, FunctionBody::Todo));
        fun.body = FunctionBody::Known(body);
    }
    pub fn finish(self) -> HandleVec<FunctionHandle, Function> {
        self.functions
    }
}

impl Display for ModuleBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut w = ExprPrinter::new(self, f);
        let mut first = true;
        for fun in &self.functions {
            if !first {
                write!(w, "\n\n")?;
            }
            first = false;
            write!(w, "fn {}", fun.name)?;
            w.fmt_enclosed_delimited_generic(
                &fun.args,
                |el, i, w| {
                    let name = el.get_name(self);
                    write!(w, "v{i}: {name}",)
                },
                "(",
                ")",
                ",",
                false,
            )?;
            if fun.ret != ExprType::Void {
                write!(w, " -> {}", fun.ret.get_name(self))?;
            }
            write!(w, " ")?;
            match &fun.body {
                FunctionBody::Builtin => {
                    w.push();
                    write!(w, "{{\nunreachable!(\"Builtin\")")?;
                    w.pop();
                    write!(w, "\n}}")?;
                }
                FunctionBody::Todo => {
                    w.push();
                    write!(w, "{{\ntodo!()")?;
                    w.pop();
                    write!(w, "\n}}")?;
                }
                FunctionBody::Known(b) => b.print(&mut w)?,
            }
        }
        Ok(())
    }
}

pub struct FunctionBuilder {
    arg_count: usize,
    variable_counter: Cell<usize>,
    block_counter: Cell<usize>,
}

impl FunctionBuilder {
    pub fn new(function: FunctionHandle, module: &ModuleBuilder) -> FunctionBuilder {
        let fun = &module.functions[function];
        let arg_count = fun.args.len();
        Self {
            arg_count,
            variable_counter: Cell::new(arg_count),
            block_counter: Cell::new(0),
        }
    }
    pub fn parameters_iter(
        &self,
    ) -> std::iter::Map<std::ops::Range<usize>, fn(usize) -> VariableHandle> {
        (0..self.arg_count).map(VariableHandle::new)
    }
    pub fn get_parameter(&self, index: usize) -> Option<VariableHandle> {
        if index < self.arg_count {
            Some(VariableHandle::new(index))
        } else {
            None
        }
    }
    pub fn new_variable(&self) -> VariableHandle {
        let c = self.variable_counter.get();
        self.variable_counter.set(c + 1);
        VariableHandle::new(c)
    }
    pub fn new_block(&self) -> BlockHandle {
        let c = self.block_counter.get();
        self.block_counter.set(c + 1);
        BlockHandle::new(c)
    }
    pub fn new_block_builder(&self) -> BlockBuilder {
        BlockBuilder::new(self)
    }
}

pub fn generate_functions(
    converted: &ConvertedFile,
    lowered: &LoweredFile,
    compiled: &CompiledFile,
) -> (ModuleBuilder, GenerationContext, Vec<SpannedError>) {
    let mut module = ModuleBuilder::new();
    let parser = ExprType::Custom(module.register_type("Parser"));
    let checkpoint = ExprType::Custom(module.register_type("Checkpoint"));
    let span_start = ExprType::Custom(module.register_type("Position"));

    let fn_expect = module.builtin_fn("expect", &[parser, ExprType::SpanKind], ExprType::Bool);
    let fn_token_any = module.builtin_fn("token_any", &[parser], ExprType::Bool);
    let fn_token_not =
        module.builtin_fn("token_not", &[parser, ExprType::SpanKind], ExprType::Bool);
    let fn_make_checkpoint = module.builtin_fn("checkpoint", &[parser], checkpoint);
    let fn_restore_checkpoint = module.builtin_fn("restore", &[parser, checkpoint], ExprType::Void);
    let fn_start_span = module.builtin_fn("start_span", &[parser], span_start);
    let fn_close_span = module.builtin_fn(
        "close_span",
        &[parser, span_start, ExprType::SpanKind],
        ExprType::Void,
    );
    let fn_report_err = module.builtin_fn("report_err", &[parser, ExprType::String], span_start);
    let fn_report_err_since = module.builtin_fn(
        "report_err_since",
        &[parser, span_start, ExprType::String],
        span_start,
    );

    let mut counter = 0u32;
    let token_kinds = lowered.tokens.map_ref(|_| {
        let copy = counter;
        counter += 1;
        copy
    });
    let rule_data =
        SecondaryVec::from_iter(converted.rules.iter_kv().filter(|(_, v)| !v.inline).map(
            |(k, conv)| {
                let function = if conv.attributes.pratt {
                    let name = format!("{}_pratt", conv.name);
                    module.predeclare_fn(&name, &[parser, ExprType::U32], ExprType::Bool)
                } else {
                    module.predeclare_fn(&conv.name, &[parser], ExprType::Bool)
                };
                let data = RuleData {
                    function,
                    kind: counter,
                };
                counter += 1;
                (k, data)
            },
        ));

    let cx = GenerationContext {
        token_kinds,
        rule_data,
        fn_expect,
        fn_token_any,
        fn_token_not,
        fn_make_checkpoint,
        fn_restore_checkpoint,
        fn_start_span,
        fn_close_span,
        fn_report_err,
        fn_report_err_since,
    };

    let mut errors = Vec::new();

    for (handle, data) in cx.rule_data.iter_kv() {
        let function = FunctionBuilder::new(data.function, &mut module);

        let mut expr = if converted.rules[handle].attributes.pratt {
            let CompiledRule::Pratt(children) = &compiled.rules[handle] else {
                unreachable!()
            };
            generate_pratt_expr(
                &function,
                handle,
                children,
                compiled,
                converted,
                &mut errors,
                &cx,
            )
        } else {
            let expr = match &compiled.rules[handle] {
                CompiledRule::Unchanged => &lowered.rules[handle],
                CompiledRule::PrattChild(a) => a,
                CompiledRule::Pratt(_) => unreachable!(),
            };
            generate_expr_function(expr, &function, data, converted, &mut errors, &cx)
        };

        let mut rewriting = RewriteCx::new(&function);
        rewrite_scope(&mut expr, &mut rewriting);
        rewriting.apply_renames(&mut expr);
        module.finish_fn(data.function, expr);
    }

    (module, cx, errors)
}

fn generate_expr_function(
    expr: &RuleExpr,
    function: &FunctionBuilder,
    data: &RuleData,
    converted: &ConvertedFile,
    errors: &mut Vec<SpannedError>,
    cx: &GenerationContext,
) -> Expr {
    let parser_var = function.get_parameter(0).unwrap();

    let mut body = function.new_block_builder();
    let start_var = body.Let(expr::Call(
        cx.fn_start_span,
        vec![expr::Variable(parser_var)],
    ));

    let mut pass = function.new_block_builder();
    {
        pass.Call(
            cx.fn_close_span,
            vec![
                expr::Variable(parser_var),
                expr::Variable(start_var),
                expr::Constant_SpanKind(data.kind),
            ],
        );
        pass.Break(body.get_handle(), expr::Constant_bool(true));
    }

    let expr = generate_expr(expr, parser_var, &function, converted, errors, cx);
    let block_handle = body.get_handle();
    body.IfElse(
        expr,
        pass.finish(),
        expr::Break(block_handle, expr::Constant_bool(false)),
    );

    body.finish()
}

pub struct RuleData {
    pub function: FunctionHandle,
    pub kind: u32,
}

pub struct GenerationContext {
    pub token_kinds: HandleVec<crate::convert::TokenHandle, u32>,
    pub rule_data: SecondaryVec<crate::convert::RuleHandle, RuleData>,
    pub fn_expect: FunctionHandle,
    pub fn_token_any: FunctionHandle,
    pub fn_token_not: FunctionHandle,
    pub fn_make_checkpoint: FunctionHandle,
    pub fn_restore_checkpoint: FunctionHandle,
    pub fn_start_span: FunctionHandle,
    pub fn_close_span: FunctionHandle,
    pub fn_report_err: FunctionHandle,
    pub fn_report_err_since: FunctionHandle,
}

/// ```
/// fn expr(p: &mut Parser, min_bp: u8) -> bool {
///     let m = p.open();
///
///     // parse choice of leaf (Atom and Prefix) expressions
///     'block: {
///         if rule1(p) {
///             break 'block;
///         }
///         if rule2(p) {
///             break 'block;
///         }
///         return false;
///     }
///
///     // parse Postfix or Binary expressions
///     // at this point we've consumed the leading Expression, we need to inline all the patterns excluding the start
///     'consume: loop {
///         'block: {
///             if bp /* bp table lookup */ < min_bp {
///                 break 'block;
///             }
///
///             if !p.token(TokenKind) {
///                 break 'block;
///             }
///             // commit
///             p.token(TokenKind);
///             p.token(TokenKind);
///             // ...
///
///             p.close(m, SpanKind);
///             continue 'consume;
///         }
///
///         'block: {
///             if bp /* bp table lookup */ < min_bp {
///                 break 'block;
///             }
///
///             if !p.token(TokenKind) {
///                 break 'block;
///             }
///             // commit
///             p.token(TokenKind);
///             p.token(TokenKind);
///             // ...
///
///             p.close(m, SpanKind);
///             continue 'consume;
///         }
///
///         break;
///     }
///
///     return true;
/// }
/// ```
fn generate_pratt_expr(
    builder: &FunctionBuilder,
    this: RuleHandle,
    children: &[PrattChild],
    compiled: &CompiledFile,
    converted: &ConvertedFile,
    errors: &mut Vec<SpannedError>,
    cx: &GenerationContext,
) -> Expr {
    let parser_var = builder.get_parameter(0).unwrap();
    let min_bp_var = builder.get_parameter(1).unwrap();

    let mut body = builder.new_block_builder();
    let start_var = body.Let(expr::Call(
        cx.fn_start_span,
        vec![expr::Variable(parser_var)],
    ));

    let parser = expr::Variable(parser_var);
    let mut base_expressions = Vec::new();
    let mut post_expressions = Vec::new();

    for expr in children {
        match expr.kind {
            PrattExprKind::Atom | PrattExprKind::Prefix => {
                let rule_expr = match expr.expr {
                    PrattExpr::Token(token) => RuleExpr::Token(token),
                    PrattExpr::Rule(rule) => RuleExpr::Rule(rule),
                };
                base_expressions.push(rule_expr);
            }
            PrattExprKind::Postfix | PrattExprKind::Binary(_) => {
                let rule_expr = match expr.expr {
                    PrattExpr::Token(_) => unreachable!("Single token should be an Atom"),
                    PrattExpr::Rule(rule) => match &compiled.rules[rule] {
                        crate::compile::CompiledRule::PrattChild(child) => child,
                        _ => unreachable!(),
                    },
                };

                let RuleExpr::Sequence(seq) = rule_expr else {
                    unreachable!("Only sequences can become anything other than Atom")
                };
                assert!(seq.len() > 1, "Malformed sequence");

                let RuleExpr::PrattRecursion {
                    pratt,
                    binding_power,
                } = seq[0]
                else {
                    unreachable!("Postfix/Binary must start with parent Expr")
                };
                assert_eq!(pratt, this);

                // strip the leading Expr
                post_expressions.push((expr, binding_power, &seq[1..]));
            }
        }
    }

    let base = match base_expressions.len() {
        0 => panic!(),
        1 => base_expressions.pop().unwrap(),
        _ => RuleExpr::Choice(base_expressions),
    };
    let base = generate_expr(&base, parser_var, builder, converted, errors, cx);

    body.IfBreakSelf(expr::Negate(base), expr::Constant_bool(false));

    let mut block = builder.new_block_builder();
    assert!(!post_expressions.is_empty());
    let checkpoint = block.Let(expr::Call(cx.fn_make_checkpoint, vec![parser]));

    let mut need_reset = false;
    for (rule, binding_power, sequence) in post_expressions {
        if need_reset {
            block.Call(
                cx.fn_restore_checkpoint,
                vec![Expr::VariableAccess(checkpoint)],
            );
        }

        let expr = match sequence {
            [one] => one.clone(),
            // FIXME do not allocate here
            _ => RuleExpr::Sequence(sequence.to_vec()),
        };

        // failing to match a single token does not generate errors and does not advance the parser
        need_reset = !matches!(expr, RuleExpr::Token(_));

        let mut subblock = builder.new_block_builder();
        subblock.IfBreakSelf(
            expr::More(
                expr::Variable(min_bp_var),
                expr::Constant_u32(binding_power),
            ),
            expr::Empty(),
        );

        let mut pass = builder.new_block_builder();
        {
            if let PrattExpr::Rule(rule) = rule.expr {
                let kind = cx.rule_data[rule].kind;
                pass.Call(
                    cx.fn_close_span,
                    vec![
                        expr::Variable(parser_var),
                        expr::Variable(start_var),
                        expr::Constant_SpanKind(kind),
                    ],
                );
            };
            pass.Continue(block.get_handle());
        }

        let expr = generate_expr(&expr, parser_var, builder, converted, errors, cx);
        subblock.If(expr, pass.finish());
        block.push(subblock.finish());
    }
    block.BreakSelf(expr::Empty());
    body.Loop(block.finish());
    body.BreakSelf(expr::Constant_bool(true));

    body.finish()
}

fn generate_expr(
    rule: &RuleExpr,
    parser_var: VariableHandle,
    builder: &FunctionBuilder,
    converted: &ConvertedFile,
    errors: &mut Vec<SpannedError>,
    cx: &GenerationContext,
) -> Expr {
    let parser = expr::Variable(parser_var);
    match rule {
        RuleExpr::Token(handle) => {
            // TODO report errors
            expr::Call(
                cx.fn_expect,
                vec![expr::Constant_SpanKind(cx.token_kinds[*handle])],
            )
        }
        RuleExpr::Rule(handle) => {
            let args = match converted.rules[*handle].attributes.pratt {
                true => vec![parser, expr::Constant_u32(0)],
                false => vec![parser],
            };
            expr::Call(cx.rule_data[*handle].function, args)
        }
        RuleExpr::Sequence(seq) => {
            // 'block: {
            //     if !rule1(parser) {
            //         break 'block false;
            //     }
            //     rule2(parser);
            //     rule3(parser);
            //     break 'block true;
            // }

            assert!(!seq.is_empty());
            let mut block = builder.new_block_builder();

            let mut commited = false;
            for a in seq {
                let expr: Expr = generate_expr(a, parser_var, builder, converted, errors, cx);
                if commited {
                    block.push(expr);
                } else {
                    // TODO manual commits
                    commited = true;
                    block.IfBreakSelf(expr::Negate(expr), expr::Constant_bool(false));
                }
            }
            block.BreakSelf(expr::Constant_bool(true));
            block.finish()
        }
        RuleExpr::Choice(seq) => {
            // 'block: {
            //     let checkpoint = make_checkpoint(parser);
            //     if rule1(parser) {
            //         break 'block true;
            //     }
            //     restore_checkpoint(parser, checkpoint);
            //     if rule2(parser) {
            //         break 'block true;
            //     }
            //     break 'block false;
            // }

            assert!(!seq.is_empty());
            let mut block = builder.new_block_builder();
            let checkpoint = block.Let(expr::Call(cx.fn_make_checkpoint, vec![parser]));

            let mut need_reset = false;
            for a in seq {
                if need_reset {
                    block.Call(
                        cx.fn_restore_checkpoint,
                        vec![Expr::VariableAccess(checkpoint)],
                    );
                }
                need_reset = !matches!(a, RuleExpr::Token(_));

                let expr = generate_expr(a, parser_var, builder, converted, errors, cx);
                block.IfBreakSelf(expr, expr::Constant_bool(true));
            }
            block.BreakSelf(expr::Constant_bool(false));
            block.finish()
        }
        RuleExpr::Loop(a) => {
            // 'block: {
            //     while rule1(parser) {}
            //     break 'block true;
            // }

            let mut block = builder.new_block_builder();

            let expr = generate_expr(a, parser_var, builder, converted, errors, cx);
            block.While(expr, expr::Empty());
            block.BreakSelf(expr::Constant_bool(true));
            block.finish()
        }
        RuleExpr::OneOrMore(a) => {
            // 'block: {
            //     let mut correct = false;
            //     while rule1(parser) {
            //         correct = true;
            //     }
            //     if !correct {
            //         report_error(parser);
            //     }
            //     break 'block correct;
            // }

            let mut block = builder.new_block_builder();

            let expr = generate_expr(a, parser_var, builder, converted, errors, cx);
            let correct = block.LetMut(expr::Constant_bool(false));
            block.While(expr, expr::AssignVar(correct, expr::Constant_bool(true)));
            block.If(
                expr::Negate(expr::Variable(correct)),
                expr::Call(
                    cx.fn_report_err,
                    vec![expr::Constant_str("Expected TODO kind name")],
                ),
            );
            block.BreakSelf(expr::Variable(correct));
            block.finish()
        }
        RuleExpr::Maybe(a) => {
            // 'block: {
            //     let checkpoint = make_checkpoint(parser);
            //     if !rule1(parser) {
            //         restore_checkpoint(parser, checkpoint);
            //     }
            //     break 'block true;
            // }

            let mut block = builder.new_block_builder();
            let expr = generate_expr(a, parser_var, builder, converted, errors, cx);
            if let RuleExpr::Token(_) = a.as_ref() {
                block.push(expr);
            } else {
                let checkpoint = block.Let(expr::Call(cx.fn_make_checkpoint, vec![parser.clone()]));
                block.If(
                    expr::Negate(expr),
                    expr::Call(
                        cx.fn_restore_checkpoint,
                        vec![parser, expr::Variable(checkpoint)],
                    ),
                );
            }
            block.BreakSelf(expr::Constant_bool(true));
            block.finish()
        }
        RuleExpr::Any => {
            // token_any(parser)
            expr::Call(cx.fn_token_any, vec![parser])
        }
        RuleExpr::Not(token) => {
            // token_not(parser, TokenKind)

            if let RuleExpr::Token(token) = token.as_ref() {
                expr::Call(
                    cx.fn_token_not,
                    vec![parser, expr::Constant_SpanKind(cx.token_kinds[*token])],
                )
            } else {
                errors.push(SpannedError {
                    span: StrSpan::empty(),
                    err: "RuleExpr::Not expects a single token".to_owned(),
                });
                expr::Error()
            }
        }
        RuleExpr::SeparatedList { element, separator } => {
            // 'block: loop {
            //     if !rule1(parser) {
            //         break 'block true;
            //     }
            //     if !rule2(parser) {
            //         break 'block true;
            //     }
            // }

            let mut block = builder.new_block_builder();
            let element = generate_expr(element, parser_var, builder, converted, errors, cx);
            let separator = generate_expr(separator, parser_var, builder, converted, errors, cx);

            block.IfBreakSelf(expr::Negate(element), expr::Constant_bool(true));
            block.IfBreakSelf(expr::Negate(separator), expr::Constant_bool(true));
            expr::Loop(block.finish())
        }
        RuleExpr::PrattRecursion {
            pratt,
            binding_power,
        } => expr::Call(
            cx.rule_data[*pratt].function,
            vec![parser, expr::Constant_u32(*binding_power)],
        ),
        RuleExpr::ZeroSpace => todo!(),
        // TODO this pattern matches without consuming anything, this will lead to infinite loops
        // what do?
        RuleExpr::Empty => expr::Constant_bool(true),
        RuleExpr::Error => expr::Error(),
        RuleExpr::InlineParameter(_) => unreachable!(),
        RuleExpr::InlineCall(_) => unreachable!(),
    }
}

// enum VariableState {
//     Unitialized,
//     OutOfScope,
//     Unknown,
//     Known(ExprConstant),
// }

// struct LiveVariables {
//     variables: SecondaryVec<VariableHandle, (VariableState, ExprType)>,
//     scope_stack: Vec<Vec<VariableHandle>>,
//     cx: ConvertCtx<'static>,
// }

// impl LiveVariables {
//     pub fn new() -> LiveVariables {
//         Self {
//             variables: SecondaryVec::new(),
//             scope_stack: Vec::new(),
//             cx: ConvertCtx::new(""),
//         }
//     }
//     pub fn declare_variable(&mut self, handle: VariableHandle, ty: ExprType, expr: Option<&Expr>) {
//         if let Some(_) = self.variables.get(handle) {
//             self.cx
//                 .error(StrSpan::empty(), "duplicate variable declaration");
//         } else {
//             self.variables
//                 .insert(handle, (VariableState::Unitialized, ty));
//             if let Some(expr) = expr {
//                 self.assign_variable(handle, expr);
//             }
//         }
//     }
//     pub fn assign_variable(&mut self, handle: VariableHandle, expr: &Expr) {
//         let value = eval_expr(expr, self);
//         if let Some((var, ty)) = self.variables.get_mut(handle) {
//             *var = match value {
//                 Ok(val) => {
//                     if val.ty() == *ty {
//                         VariableState::Known(val)
//                     } else {
//                         self.cx.error(StrSpan::empty(), "types do not match");
//                         VariableState::Unknown
//                     }
//                 }
//                 _ => VariableState::Unknown,
//             }
//         } else {
//             self.cx.error(StrSpan::empty(), "variable does not exist");
//         }
//     }
//     pub fn get_variable(&self, handle: VariableHandle) -> Result<&ExprConstant, ExprEvalError> {
//         let Some((var, _)) = self.variables.get(handle) else {
//             self.cx.error(StrSpan::empty(), "variable does not exist");
//             return Err(ExprEvalError::Error);
//         };
//         match var {
//             VariableState::Unitialized => {
//                 self.cx
//                     .error(StrSpan::empty(), "accessing unitialized variable");
//                 Err(ExprEvalError::Error)
//             }
//             VariableState::OutOfScope => Err(ExprEvalError::Error),
//             VariableState::Unknown => Err(ExprEvalError::ValueUnknown),
//             VariableState::Known(val) => Ok(val),
//         }
//     }
// }

// enum ExprEvalError {
//     ValueUnknown,
//     InvalidOperation,
//     Error,
// }

// fn eval_expr(expr: &Expr, vars: &mut LiveVariables) -> Result<ExprConstant, ExprEvalError> {
//     fn u32_binop(
//         a: &Expr,
//         b: &Expr,
//         vars: &mut LiveVariables,
//         fun: fn(u32, u32) -> bool,
//     ) -> Result<ExprConstant, ExprEvalError> {
//         let a = eval_expr(a, vars)?;
//         let b = eval_expr(b, vars)?;
//         match (a, b) {
//             (ExprConstant::U32(a), ExprConstant::U32(b)) => Ok(ExprConstant::Bool(fun(a, b))),
//             _ => Err(ExprEvalError::InvalidOperation),
//         }
//     }
//     fn expr_equal(a: &Expr, b: &Expr, vars: &mut LiveVariables) -> Result<bool, ExprEvalError> {
//         let a = eval_expr(a, vars)?;
//         let b = eval_expr(b, vars)?;
//         match (a, b) {
//             (ExprConstant::Void, ExprConstant::Void) => Ok(true),
//             (ExprConstant::Bool(a), ExprConstant::Bool(b)) => Ok(a == b),
//             (ExprConstant::U32(a), ExprConstant::U32(b)) => Ok(a == b),
//             (ExprConstant::SpanKind(a), ExprConstant::SpanKind(b)) => Ok(a == b),
//             (ExprConstant::String(a), ExprConstant::String(b)) => Ok(a == b),
//             _ => Err(ExprEvalError::InvalidOperation),
//         }
//     }

//     match expr {
//         Expr::Error => Err(ExprEvalError::Error),
//         Expr::Empty => Ok(ExprConstant::Void),
//         Expr::Negate(a) => match eval_expr(a, vars)? {
//             ExprConstant::Bool(bool) => Ok(ExprConstant::Bool(!bool)),
//             _ => Err(ExprEvalError::InvalidOperation),
//         },
//         Expr::LessOrEqual(a, b) => u32_binop(a, b, vars, |a, b| a <= b),
//         Expr::MoreOrEqual(a, b) => u32_binop(a, b, vars, |a, b| a >= b),
//         Expr::Less(a, b) => u32_binop(a, b, vars, |a, b| a <= b),
//         Expr::More(a, b) => u32_binop(a, b, vars, |a, b| a <= b),
//         Expr::Equal(a, b) => expr_equal(a, b, vars).map(ExprConstant::Bool),
//         Expr::NotEqual(a, b) => expr_equal(a, b, vars).map(|bool| ExprConstant::Bool(!bool)),
//         Expr::VariableAccess(handle) => todo!(),
//         Expr::DeclareVariable {
//             handle,
//             mutable,
//             value,
//         } => todo!(),
//         Expr::AssignVariable { handle, value } => todo!(),
//         Expr::Constant(_) => todo!(),
//         Expr::Call { fun, arguments } => todo!(),
//         Expr::If {
//             condition,
//             pass,
//             otherwise,
//         } => todo!(),
//         Expr::While { condition, block } => todo!(),
//         Expr::Loop(_) => todo!(),
//         Expr::Block { handle, statements } => todo!(),
//         Expr::Break(a, b) => todo!(),
//         Expr::Continue(_) => todo!(),
//     }
// }

// fn handle_variables(expr: &Expr, variables: HandleVec<VariableHandle, VariableState>) {
//     match expr {
//         Expr::VariableAccess(_) => todo!(),
//         Expr::DeclareVariable {
//             handle,
//             mutable,
//             value,
//         } => todo!(),
//         Expr::AssignVariable { handle, value } => todo!(),

//         Expr::Error => todo!(),
//         Expr::Empty => todo!(),
//         Expr::Negate(_) => todo!(),
//         Expr::LessOrEqual(_, _) => todo!(),
//         Expr::MoreOrEqual(_, _) => todo!(),
//         Expr::Less(_, _) => todo!(),
//         Expr::More(_, _) => todo!(),
//         Expr::Equal(_, _) => todo!(),
//         Expr::NotEqual(_, _) => todo!(),
//         Expr::Argument(_) => todo!(),
//         Expr::Constant(_) => todo!(),
//         Expr::Call { fun, arguments } => todo!(),
//         Expr::If {
//             condition,
//             pass,
//             otherwise,
//         } => todo!(),
//         Expr::While { condition, block } => todo!(),
//         Expr::Loop(_) => todo!(),
//         Expr::Block { handle, statements } => todo!(),
//         Expr::Break(_, _) => todo!(),
//         Expr::Continue(_) => todo!(),
//     }
// }

struct ScopeData {
    block_vec_start: u32,
    handle: BlockHandle,
}

struct RewriteCx<'a> {
    block_vec: BlockBuilder<'a>,
    scopes: Vec<ScopeData>,
    renamed_blocks: HashMap<BlockHandle, BlockHandle>,
}

impl<'a> RewriteCx<'a> {
    fn new(builder: &'a FunctionBuilder) -> RewriteCx<'a> {
        Self {
            block_vec: BlockBuilder::new(builder),
            scopes: Vec::new(),
            renamed_blocks: HashMap::new(),
        }
    }
    fn builder(&self) -> &FunctionBuilder {
        self.block_vec.builder
    }
    fn block(&mut self) -> &mut BlockBuilder<'a> {
        &mut self.block_vec
    }
    fn rename_block(&mut self, from: BlockHandle, to: BlockHandle) {
        self.renamed_blocks.insert(from, to);
    }
    fn get_renamed_block(&mut self, handle: BlockHandle) -> BlockHandle {
        match self.renamed_blocks.get(&handle).cloned() {
            Some(found) => {
                let next = self.get_renamed_block(found);
                if found != next {
                    self.renamed_blocks.insert(handle, next);
                }
                next
            }
            None => handle,
        }
    }
    fn apply_renames(&mut self, expr: &mut Expr) {
        visit_exprs_top_down(expr, |expr| {
            if let Expr::Break(block, _) | Expr::Continue(block) = expr {
                *block = self.get_renamed_block(*block);
            }
            Ok(())
        });
    }
    fn enter_scope(&mut self, handle: BlockHandle) {
        let scope = ScopeData {
            block_vec_start: self.block_vec.sequence.len() as u32,
            handle,
        };
        self.scopes.push(scope);
    }
    fn push_expr(&mut self, expr: Expr) {
        self.block().push(expr);
    }
    #[must_use]
    fn leave_scope(&mut self) -> Expr {
        let scope = self.scopes.pop().unwrap();
        let start = scope.block_vec_start as usize;
        match self.block_vec.sequence.len() - start {
            0 => Expr::Empty,
            // 1 => self.block_vec.sequence.pop().unwrap(),
            _ => {
                let statements = self.block_vec.sequence.drain(start..).collect();
                Expr::Block {
                    handle: scope.handle,
                    statements,
                }
            }
        }
    }
}

fn visit_exprs_top_down(expr: &mut Expr, mut fun: impl FnMut(&mut Expr) -> Result<(), ()>) {
    visit_exprs_(expr, true, &mut fun);
}

fn visit_exprs_bottom_up(expr: &mut Expr, mut fun: impl FnMut(&mut Expr) -> Result<(), ()>) {
    visit_exprs_(expr, false, &mut fun);
}

fn visit_exprs_(
    expr: &mut Expr,
    top_down: bool,
    fun: &mut dyn FnMut(&mut Expr) -> Result<(), ()>,
) -> Result<(), ()> {
    if top_down {
        fun(expr)?;
    }
    match expr {
        Expr::Error
        | Expr::Empty
        | Expr::Continue(_)
        | Expr::VariableAccess(_)
        | Expr::Constant(_) => {}
        Expr::Negate(a)
        | Expr::Loop(a)
        | Expr::Break(_, a)
        | Expr::AssignVariable { value: a, .. } => {
            visit_exprs_(a, top_down, fun)?;
        }
        Expr::LessOrEqual(a, b)
        | Expr::MoreOrEqual(a, b)
        | Expr::Less(a, b)
        | Expr::More(a, b)
        | Expr::Equal(a, b)
        | Expr::NotEqual(a, b) => {
            visit_exprs_(a, top_down, fun)?;
            visit_exprs_(b, top_down, fun)?;
        }
        Expr::DeclareVariable {
            handle,
            mutable,
            value,
        } => {
            if let Some(a) = value {
                visit_exprs_(a, top_down, fun)?;
            }
        }
        Expr::Call { arguments, .. } => {
            for a in arguments {
                visit_exprs_(a, top_down, fun)?;
            }
        }
        Expr::If {
            condition,
            pass,
            otherwise,
        } => {
            visit_exprs_(condition, top_down, fun)?;
            visit_exprs_(pass, top_down, fun)?;
            if let Some(a) = otherwise {
                visit_exprs_(a, top_down, fun)?;
            }
        }
        Expr::While { condition, block } => {
            visit_exprs_(condition, top_down, fun)?;
            visit_exprs_(block, top_down, fun)?;
        }
        Expr::Block { statements, .. } => {
            for a in statements {
                visit_exprs_(a, top_down, fun)?;
            }
        }
    }
    if !top_down {
        fun(expr)?;
    }
    Ok(())
}

fn outline_expr(expr: &mut Expr, rewriting: &mut RewriteCx) {
    visit_exprs_top_down(expr, |expr| {
        match expr {
            Expr::If { .. } | Expr::While { .. } | Expr::Loop(_) | Expr::Block { .. } => {
                let handle = rewriting.builder().new_variable();
                let this = std::mem::replace(expr, Expr::VariableAccess(handle));
                let mut decl = Expr::DeclareVariable {
                    handle,
                    mutable: false,
                    value: Some(Box::new(this)),
                };
                rewrite_expr(&mut decl, rewriting);
            }
            _ => {}
        }
        Ok(())
    });
}

fn get_condition_truthy_value(expr: &mut Expr) -> Option<(bool, &mut Expr)> {
    match expr {
        Expr::Negate(a) => get_condition_truthy_value(a).map(|(bool, handle)| (!bool, handle)),
        Expr::Block { .. } => Some((true, expr)),
        _ => None,
    }
}

fn rewrite_expr(expr: &mut Expr, rewriting: &mut RewriteCx) {
    match expr {
        Expr::If {
            condition,
            pass,
            otherwise,
        } => {
            // constant fold simple cases
            let known_bool = match condition.as_ref() {
                Expr::Constant(ExprConstant::Bool(bool)) => Some(*bool),
                Expr::Negate(negate) => {
                    if let Expr::Constant(ExprConstant::Bool(bool)) = negate.as_ref() {
                        Some(!*bool)
                    } else {
                        None
                    }
                }
                _ => None,
            };

            if let Some(bool) = known_bool {
                let replacement = match bool {
                    true => Some(&mut **pass),
                    false => otherwise.as_deref_mut(),
                };
                if let Some(expr) = replacement {
                    rewrite_expr(expr, rewriting);
                }
                return;
            } else {
                let branches_inlinable = true /* TODO */;
                let truth_value = branches_inlinable
                    .then(|| get_condition_truthy_value(condition))
                    .flatten();

                if let Some((truth, condition)) = truth_value {
                    let handle = match condition {
                        Expr::Block { handle, .. } => *handle,
                        _ => unreachable!(),
                    };
                    let leave = Expr::Break(handle, Box::new(Expr::Empty));

                    _ = patch_to_escape(pass, &leave, rewriting.builder(), true);
                    let otherwise = match otherwise {
                        Some(expr) => {
                            _ = patch_to_escape(expr, &leave, rewriting.builder(), true);
                            expr
                        }
                        None => &leave,
                    };

                    visit_exprs_top_down(condition, |expr| {
                        if let Expr::Break(block, inner) = expr {
                            if *block == handle {
                                if let Expr::Constant(ExprConstant::Bool(bool)) = inner.as_ref() {
                                    if *bool == truth {
                                        *expr = pass.as_ref().clone();
                                    } else {
                                        *expr = otherwise.clone();
                                    }
                                } else {
                                    let inner = std::mem::replace(&mut **inner, Expr::Empty);
                                    *expr = Expr::If {
                                        condition: Box::new(inner),
                                        pass: pass.clone(),
                                        otherwise: Some(Box::new(otherwise.clone())),
                                    }
                                }
                            }
                            Err(())
                        } else {
                            Ok(())
                        }
                    });
                    rewrite_expr(condition, rewriting);
                    return;
                } else {
                    outline_expr(condition, rewriting);
                    rewrite_scope(pass, rewriting);
                    if let Some(otherwise) = otherwise {
                        rewrite_scope(otherwise, rewriting);
                    }
                }
            }
        }
        // FIXME outlining with while loops will need replacing them with simple loops
        Expr::While { block, .. } | Expr::Loop(block) => rewrite_scope(block, rewriting),
        Expr::Block { .. } => rewrite_scope(expr, rewriting),
        Expr::Break(_, a) => outline_expr(a, rewriting),
        Expr::Continue(_) => {}
        _ => {}
    }
    rewriting.push_expr(std::mem::replace(expr, Expr::Error));
}

/// Appends `with` to places where the control flow ends
fn patch_to_escape(
    expr: &mut Expr,
    with: &Expr,
    builder: &FunctionBuilder,
    add_block: bool,
) -> Result<(), ()> {
    match expr {
        Expr::If {
            condition,
            otherwise,
            ..
        } => {
            _ = patch_to_escape(condition, with, builder, true);
            if let Some(some) = otherwise {
                _ = patch_to_escape(some, with, builder, add_block);
            } else {
                *otherwise = Some(Box::new(with.clone()))
            }
            Ok(())
        }
        Expr::Block { statements, .. } => {
            match statements.last() {
                Some(Expr::Break(..) | Expr::Continue(_)) => {}
                _ => {
                    statements.push(with.clone());
                }
            }
            Ok(())
        }
        Expr::Break(..) | Expr::Continue(_) => Ok(()),
        _ => {
            if add_block {
                let handle = builder.new_block();
                let inner = std::mem::replace(
                    expr,
                    Expr::Block {
                        handle,
                        statements: Vec::new(),
                    },
                );

                let Expr::Block { statements, .. } = expr else {
                    unreachable!()
                };
                statements.push(inner);
                statements.push(with.clone());
                Ok(())
            } else {
                Err(())
            }
        }
    }
}

fn inline_block(parent: BlockHandle, statements: Vec<Expr>, rewriting: &mut RewriteCx<'_>) {
    let mut parent_statements = statements;
    'outer: loop {
        for expr in &mut parent_statements {
            rewrite_expr(expr, rewriting);
        }
        loop {
            let BlockBuilder {
                builder,
                statements,
                ..
            } = rewriting.block();
            match statements.sequence.as_mut_slice() {
                [.., Expr::Block { .. }] => {
                    let Expr::Block { handle, statements } =
                        rewriting.block_vec.sequence.pop().unwrap()
                    else {
                        unreachable!()
                    };
                    rewriting.rename_block(handle, parent);
                    parent_statements = statements;
                    continue 'outer;
                }
                [.., block @ Expr::Block { .. }, leave @ (Expr::Break(_, _) | Expr::Continue(_))] =>
                {
                    let Expr::Block { handle, .. } = *block else {
                        unreachable!()
                    };
                    // TODO do not traverse the whole tree every time
                    visit_exprs_top_down(block, |expr| {
                        if let Expr::Break(original, _) = expr {
                            if *original == handle {
                                *expr = leave.clone();
                            }
                            Err(())
                        } else {
                            Ok(())
                        }
                    });
                    _ = patch_to_escape(block, leave, builder, true);
                    statements.sequence.pop();
                    continue;
                }
                _ => {}
            }
            break 'outer;
        }
    }
}

fn rewrite_scope(expr: &mut Expr, rewriting: &mut RewriteCx<'_>) {
    if let Expr::Block { handle, statements } = expr {
        rewriting.enter_scope(*handle);
        inline_block(*handle, std::mem::take(statements), rewriting);
    } else {
        let handle = rewriting.builder().new_block();
        rewriting.enter_scope(handle);
        rewrite_expr(expr, rewriting);
    };

    *expr = rewriting.leave_scope();
}

simple_handle! {
    pub CfgBlockHandle,
    pub CfgVariableHandle
}

enum MonoOp {
    Negate,
}

enum BinOp {
    Equal,
    NotEqual,
    Less,
    LessEq,
    More,
    MoreEq,
}

enum StatementValue {
    Const(ExprConstant),
    Call {
        function: FunctionHandle,
        arguments: Vec<CfgVariableHandle>,
    },
    MonoOp(MonoOp, CfgVariableHandle),
    BinOp(BinOp, CfgVariableHandle, CfgVariableHandle),
}

enum Statement {
    CreateVariable(CfgVariableHandle),
    DestroyVariable(CfgVariableHandle),
    AssignVariable(CfgVariableHandle, StatementValue),
    Statement(StatementValue),
}

enum Terminator {
    IfElse {
        pass: CfgBlockHandle,
        fail: Option<CfgBlockHandle>,
    },
    Break {
        block: CfgBlockHandle,
        value: Option<ExprConstant>,
    },
    Todo,
}

struct CfgBlock {
    statements: Vec<Statement>,
    terminating_value: Option<ExprConstant>,
    terminator: CfgBlockHandle,
}

impl CfgBlock {
    fn add_create_variable(&mut self, builder: &mut CfgBuilder) -> CfgVariableHandle {
        let handle = builder.new_variable_handle();
        self.statements.push(Statement::CreateVariable(handle));
        handle
    }
    fn add_destroy_variable(&mut self, variable: CfgVariableHandle) {
        self.statements.push(Statement::DestroyVariable(variable));
    }
}

struct CfgBuilder {
    block_counter: HandleCounter<CfgBlockHandle>,
    variable_counter: HandleCounter<CfgVariableHandle>,
    blocks: HandleVec<CfgBlockHandle, CfgBlock>,
    current_block: CfgBlockHandle,
    scopes: Vec<Vec<CfgVariableHandle>>,
}

impl CfgBuilder {
    fn new_variable_handle(&mut self) -> CfgVariableHandle {
        self.variable_counter.next()
    }
    fn new_block_handle(&mut self) -> CfgBlockHandle {
        self.block_counter.next()
    }
    fn open_scope(&mut self) {
        self.scopes.push(Vec::new())
    }
    fn create_variable(&mut self) -> CfgVariableHandle {
        let handle = self.current_block().add_create_variable(self);
        self.scopes.last_mut().unwrap().push(handle);
        handle
    }
    fn close_scope(&mut self) {
        let scope = self.scopes.pop().unwrap();
        let block = self.current_block();
        for var in scope {
            block.add_destroy_variable(var);
        }
    }
    fn current_block(&mut self) -> &mut CfgBlock {
        &mut self.blocks[self.current_block]
    }
    fn connect_goto(&mut self, from: CfgBlockHandle, to: CfgBlockHandle) {}
}

fn ast_to_cfg(ast: &Expr, cfg: &mut CfgBuilder) {
    let Expr::Block { handle, statements } = ast else {
        panic!()
    };
}
