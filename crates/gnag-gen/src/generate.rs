use bumpalo::Bump;
use gnag::{
    handle::{HandleCounter, HandleVec, TypedHandle},
    simple_handle,
};

use crate::{
    compile::CompiledFile,
    convert::{ConvertedFile, RuleExpr},
    lower::LoweredFile,
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
    name: String,
    args: Vec<ExprType>,
    ret: ExprType,

    body: FunctionBody,
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

#[derive(Clone, Copy, Debug)]
pub enum ExprType {
    Never,
    Void,
    Bool,
    U32,
    SpanKind,
    Custom(CustomTypeHandle),
}

#[derive(Clone, Debug)]
pub enum ExprConstant {
    Bool(bool),
    U32(u32),
    SpanKind(u32),
}

impl ExprConstant {
    pub fn ty(&self) -> ExprType {
        match self {
            ExprConstant::Bool(_) => ExprType::Bool,
            ExprConstant::U32(_) => ExprType::U32,
            ExprConstant::SpanKind(_) => ExprType::SpanKind,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    Negate(Box<Expr>),
    Argument(u32),
    VariableAccess(VariableHandle),
    DeclareVariable {
        handle: VariableHandle,
        mutable: bool,
        value: Box<Expr>,
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
    Return(Box<Expr>),
}

pub struct ModuleBuilder {
    custom_types: HandleVec<CustomTypeHandle, String>,
    functions: HandleVec<FunctionHandle, Function>,
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
    pub fn finish(self) -> HandleVec<FunctionHandle, Function> {
        self.functions
    }
}

pub struct FunctionBuilder<'a> {
    module: &'a mut ModuleBuilder,
    function: FunctionHandle,
    variable_counter: usize,
    block_counter: usize,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(function: FunctionHandle, module: &'a mut ModuleBuilder) -> FunctionBuilder {
        let fun = &module.functions[function];
        let variable_counter = fun.args.len();

        Self {
            module,
            function,
            variable_counter,
            block_counter: 0,
        }
    }
    pub fn variables_for_arguments(
        &self,
    ) -> std::iter::Map<std::ops::Range<usize>, fn(usize) -> VariableHandle> {
        let fun = &self.module.functions[self.function];
        let args = fun.args.len();

        (0..args).map(VariableHandle::new)
    }
    pub fn new_variable(&mut self) -> VariableHandle {
        let c = self.variable_counter;
        self.variable_counter += 1;
        VariableHandle::new(c)
    }
    pub fn new_block(&mut self) -> BlockHandle {
        let c = self.block_counter;
        self.block_counter += 1;
        BlockHandle::new(c)
    }
    pub fn finish(self, predeclared: FunctionHandle, body: Expr) {
        let fun = &mut self.module.functions[predeclared];
        assert!(matches!(fun.body, FunctionBody::Todo));

        fun.body = FunctionBody::Known(body);
    }
}

pub fn generate_functions(
    converted: &ConvertedFile,
    lowered: &LoweredFile,
    compiled: &CompiledFile,
) -> HandleVec<FunctionHandle, Function> {
    let mut module = ModuleBuilder::new();
    let parser = ExprType::Custom(module.register_type("Parser"));
    let checkpoint = ExprType::Custom(module.register_type("Checkpoint"));
    let span_start = ExprType::Custom(module.register_type("Position"));

    let fn_expect = module.builtin_fn("expect", &[parser, ExprType::SpanKind], ExprType::Bool);
    let fn_make_checkpoint = module.builtin_fn("checkpoint", &[parser], checkpoint);
    let fn_restore_checkpoint = module.builtin_fn("restore", &[parser, checkpoint], ExprType::Void);
    let fn_start_span = module.builtin_fn("start_span", &[parser], span_start);

    let mut counter = 0u32;
    let token_kinds = lowered.tokens.map_ref(|_| {
        let copy = counter;
        counter += 1;
        copy
    });
    let rule_kinds = lowered.rules.map_ref(|_| {
        let copy = counter;
        counter += 1;
        copy
    });
    let rule_functions = converted
        .rules
        .map_ref(|conv| module.predeclare_fn(&conv.name, &[], ExprType::Bool));

    let context = GenerationContext {
        token_kinds,
        rule_functions,
        fn_expect,
        fn_make_checkpoint,
        fn_restore_checkpoint,
    };

    for (rule_handle, rule) in compiled.rules.iter_kv() {
        let mut builder = FunctionBuilder::new(todo!(), &mut module);
        let parser_var = builder.variables_for_arguments().next().unwrap();

        let out = generate_expr(rule,);
    }

    (C⇒D)⇒(¬D⇒¬C)    fn_restore_checkpoint: FunctionHandle,
}

fn generate_expr(
    rule: &RuleExpr,
    parser_var: VariableHandle,
    builder: &mut FunctionBuilder,
    cx: &GenerationContext,
) -> Expr {
    match rule {
        RuleExpr::Token(handle) => Expr::Call {
            // expect(parser, TokenKind)
            fun: cx.fn_expect,
            arguments: vec![Expr::Constant(ExprConstant::SpanKind(
                cx.token_kinds[*handle],
            ))],
        },
        RuleExpr::Rule(handle) => Expr::Call {
            // rule1(parser)
            fun: cx.rule_functions[*handle],
            arguments: vec![Expr::VariableAccess(parser_var)],
        },
        RuleExpr::Sequence(seq) => {
            // 'block: {
            //     if !rule1(parser) {
            //         break 'block false;
            //     }
            //     rule2(parser);
            //     rule2(parser);
            //     break 'block true;
            // }

            assert!(!seq.is_empty());
            let block = builder.new_block();

            let mut commited = true;
            let mut statements = Vec::new();
            for a in seq {
                let expr: Expr = generate_expr(a, parser_var, builder, cx);
                let expr = if commited {
                    expr
                } else {
                    // TODO manual commits
                    commited = true;
                    Expr::If {
                        condition: Box::new(Expr::Negate(Box::new(expr))),
                        pass: Box::new(Expr::Break(
                            block,
                            Box::new(Expr::Constant(ExprConstant::Bool(false))),
                        )),
                        otherwise: None,
                    }
                };
                statements.push(expr);
            }
            statements.push(Expr::Break(
                block,
                Box::new(Expr::Constant(ExprConstant::Bool(true))),
            ));

            Expr::Block {
                handle: block,
                statements,
            }
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
            let block = builder.new_block();

            let mut statements = Vec::new();
            let checkpoint = builder.new_variable();
            statements.push(Expr::DeclareVariable {
                handle: checkpoint,
                mutable: false,
                value: Box::new(Expr::Call {
                    fun: cx.fn_make_checkpoint,
                    arguments: vec![Expr::VariableAccess(parser_var)],
                }),
            });
            let mut first = true;
            for a in seq {
                if !first {
                    statements.push(Expr::Call {
                        fun: cx.fn_restore_checkpoint,
                        arguments: vec![Expr::VariableAccess(checkpoint)],
                    })
                }
                first = false;

                let expr = generate_expr(a, parser_var, builder, cx);
                let block = builder.new_block();

                statements.push(Expr::If {
                    condition: Box::new(expr),
                    pass: Box::new(Expr::Break(
                        block,
                        Box::new(Expr::Constant(ExprConstant::Bool(true))),
                    )),
                    otherwise: None,
                });
            }

            statements.push(Expr::Break(
                block,
                Box::new(Expr::Constant(ExprConstant::Bool(false))),
            ));

            Expr::Block {
                handle: block,
                statements,
            }
        }
        RuleExpr::ZeroOrMore(a) => {
            // 'block: {
            //     while rule1(parser) {}
            //     break 'block true;
            // }

            let block = builder.new_block();

            let expr = generate_expr(a, parser_var, builder, cx);
            let statements = vec![
                Expr::While {
                    condition: Box::new(expr),
                    block: Box::new(Expr::Block {
                        handle: builder.new_block(),
                        statements: vec![],
                    }),
                },
                Expr::Break(block, Box::new(Expr::Constant(ExprConstant::Bool(false)))),
            ];

            Expr::Block {
                handle: block,
                statements,
            }
        }
        RuleExpr::OneOrMore(a) => {
            // 'block: {
            //     let mut correct = false;
            //     while rule1(parser) {
            //         correct = true;
            //     }
            //     break 'block correct;
            // }

            // TODO this doesn't create error spans
            let outer_block = builder.new_block();

            let while_block = builder.new_block();
            let is_ok = builder.new_variable();
            let expr = generate_expr(a, parser_var, builder, cx);

            let while_loop = Expr::While {
                condition: Box::new(expr),
                block: Box::new(Expr::Block {
                    handle: while_block,
                    statements: vec![Expr::AssignVariable {
                        handle: is_ok,
                        value: Box::new(Expr::Constant(ExprConstant::Bool(true))),
                    }],
                }),
            };

            Expr::Block {
                handle: outer_block,
                statements: vec![while_loop, Expr::VariableAccess(is_ok)],
            }
        }
        RuleExpr::Maybe(_) => todo!(),
        RuleExpr::InlineParameter(_) => todo!(),
        RuleExpr::InlineCall(_) => todo!(),
        RuleExpr::Any => todo!(),
        RuleExpr::Not(_) => todo!(),
        RuleExpr::SeparatedList { element, separator } => todo!(),
        RuleExpr::ZeroSpace => todo!(),
        RuleExpr::Empty => todo!(),
        RuleExpr::Error => todo!(),
        RuleExpr::PrattRecursion {
            pratt,
            binding_power,
        } => todo!(),
    }
}
