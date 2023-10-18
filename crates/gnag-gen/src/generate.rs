use bumpalo::Bump;
use gnag::{handle::HandleVec, simple_handle};

use crate::{
    compile::CompiledFile,
    convert::{ConvertedFile, RuleExpr},
    lower::LoweredFile,
};

simple_handle!(
    pub FunctionHandle,

    pub BlockHandle,
    pub StatementHandle
);

#[derive(Clone, Debug)]
pub enum FunctionBody {
    Builtin,
    Todo,
    Known {
        statements: HandleVec<StatementHandle, Statement>,
        blocks: HandleVec<BlockHandle, Vec<StatementHandle>>,
        body: BlockHandle,
    },
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
    Negate(StatementHandle),
    Constant(ExprConstant),
    Call {
        fun: FunctionHandle,
        arguments: Vec<StatementHandle>,
    },
    If {
        condition: StatementHandle,
        pass: Option<BlockHandle>,
        otherwise: Option<BlockHandle>,
    },
    Loop(BlockHandle),
    Break(BlockHandle),
    Return(StatementHandle),
}

#[derive(Clone, Debug)]
pub struct Statement {
    ty: ExprType,
    value: Expr,
}

#[derive(Default)]
pub struct ModuleBuilder {
    functions: HandleVec<FunctionHandle, Function>,
}

impl ModuleBuilder {
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
    statements: HandleVec<StatementHandle, Statement>,
    blocks: HandleVec<BlockHandle, Vec<StatementHandle>>,

    block_stack: Vec<BlockHandle>,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(module: &'a mut ModuleBuilder) -> FunctionBuilder {
        Self {
            module,
            statements: HandleVec::new(),
            blocks: HandleVec::new(),
            block_stack: Vec::new(),
        }
    }

    pub fn open_block(&mut self) -> BlockHandle {
        let block = self.blocks.push(Vec::new());
        self.block_stack.push(block);
        block
    }
    pub fn end_block(&mut self) -> BlockHandle {
        self.pop_current_block()
    }
    pub fn within_block<T>(&mut self, fun: impl FnOnce(&mut FunctionBuilder) -> T) -> BlockHandle {
        self.open_block();
        _ = fun(self);
        self.end_block()
    }

    fn get_current_block(&mut self) -> BlockHandle {
        *self.block_stack.last_mut().expect("No block is open")
    }
    fn pop_current_block(&mut self) -> BlockHandle {
        self.block_stack.pop().expect("No block is open")
    }
    fn add_statement(&mut self, statement: StatementHandle) {
        let block = self.get_current_block();
        self.blocks[block].push(statement)
    }
}

impl FunctionBuilder<'_> {
    pub fn constant(&mut self, value: ExprConstant) -> StatementHandle {
        self.expr(value.ty(), Expr::Constant(value))
    }
    pub fn call(
        &mut self,
        function: FunctionHandle,
        arguments: &[StatementHandle],
    ) -> StatementHandle {
        self.expr(
            self.module.functions[function].ret,
            Expr::Call {
                fun: function,
                arguments: arguments.to_vec(),
            },
        )
    }
    pub fn bbreak(&mut self, parent: BlockHandle) -> StatementHandle {
        self.expr(ExprType::Never, Expr::Break(parent))
    }
    pub fn bif(&mut self, condition: StatementHandle, pass: BlockHandle) -> StatementHandle {
        self.bbranch(condition, Some(pass), None)
    }
    pub fn belse(&mut self, condition: StatementHandle, pass: BlockHandle) -> StatementHandle {
        self.bbranch(condition, None, Some(pass))
    }
    pub fn bbranch(
        &mut self,
        condition: StatementHandle,
        pass: Option<BlockHandle>,
        otherwise: Option<BlockHandle>,
    ) -> StatementHandle {
        // TODO check block types
        self.expr(
            ExprType::Void,
            Expr::If {
                condition,
                pass,
                otherwise,
            },
        )
    }

    pub fn expr(&mut self, ty: ExprType, value: Expr) -> StatementHandle {
        // TODO check that type matches
        let statement = self.statements.push(Statement { ty, value });
        self.add_statement(statement);
        statement
    }
}

impl FunctionBuilder<'_> {
    /// Finish the function and
    pub fn finish_predeclared(&mut self, predeclared: FunctionHandle) {
        // TODO check predeclared return type against body
        assert_eq!(self.block_stack.len(), 1);
        let body = self.pop_current_block();

        let fun = &mut self.module.functions[predeclared];
        assert!(matches!(fun.body, FunctionBody::Todo));

        fun.body = FunctionBody::Known {
            statements: self.statements.clone(),
            blocks: self.blocks.clone(),
            body,
        };

        self.statements.clear();
        self.blocks.clear();
    }
    /// Finish the function and
    pub fn finish(&mut self, name: &str, args: &[ExprType], ret: ExprType) -> FunctionHandle {
        // TODO figure out return type?
        let predeclared = self.module.predeclare_fn(name, args, ret);
        self.finish_predeclared(predeclared);
        predeclared
    }
}

pub fn generate_functions(
    converted: &ConvertedFile,
    lowered: &LoweredFile,
    compiled: &CompiledFile,
) -> HandleVec<FunctionHandle, Function> {
    let mut module = ModuleBuilder::default();

    let expect = module.builtin_fn("expect", &[ExprType::SpanKind], ExprType::Bool);

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

    for (rule_handle, rule) in compiled.rules.iter_kv() {
        let mut parent: BlockHandle = None.unwrap();
        let mut early_exit = true;

        let mut builder = FunctionBuilder::new(&mut module);
        let body = builder.open_block();
        for stat in rule.get_sequence_slice() {
            match stat {
                RuleExpr::Token(handle) => {
                    let kind = token_kinds[*handle];
                    let constant = builder.constant(ExprConstant::SpanKind(kind));
                    builder.call(expect, &[constant]);
                }
                RuleExpr::Rule(handle) => {
                    builder.call(rule_functions[*handle], &[]);
                }
                RuleExpr::Sequence(seq) => {
                    for rule in seq {
                        let var = builder.expr(ExprType::Bool, todo!("Recursive call"));
                        if early_exit {
                            let block = builder.within_block(|builder| builder.bbreak(parent));
                            builder.belse(var, block);
                        }
                    }
                }
                RuleExpr::Choice(_) => todo!(),
                RuleExpr::ZeroOrMore(_) => todo!(),
                RuleExpr::OneOrMore(_) => todo!(),
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
    }

    module.finish()
}
