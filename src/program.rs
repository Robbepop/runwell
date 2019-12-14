

pub struct Program {
    functions: Vec<Function>,
}

pub struct FunctionId(u32);

pub struct Function {
    blocks: Vec<Block>,
}

pub struct Block {
    locals: Vec<Register>,
    body: Vec<Op>,
}
