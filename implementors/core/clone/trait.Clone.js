(function() {var implementors = {};
implementors["runwell_entity"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/struct.RawIdx.html\" title=\"struct runwell_entity::RawIdx\">RawIdx</a>","synthetic":false,"types":["runwell_entity::index::RawIdx"]},{"text":"impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/struct.Idx.html\" title=\"struct runwell_entity::Idx\">Idx</a>&lt;T&gt;","synthetic":false,"types":["runwell_entity::index::Idx"]},{"text":"impl&lt;T:&nbsp;<a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/primary/struct.EntityArena.html\" title=\"struct runwell_entity::primary::EntityArena\">EntityArena</a>&lt;T&gt;","synthetic":false,"types":["runwell_entity::primary::arena::EntityArena"]},{"text":"impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/primary/struct.PhantomEntityArena.html\" title=\"struct runwell_entity::primary::PhantomEntityArena\">PhantomEntityArena</a>&lt;T&gt;","synthetic":false,"types":["runwell_entity::primary::phantom_arena::PhantomEntityArena"]},{"text":"impl&lt;K&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/secondary/default_bitvec/struct.DefaultComponentBitVec.html\" title=\"struct runwell_entity::secondary::default_bitvec::DefaultComponentBitVec\">DefaultComponentBitVec</a>&lt;K&gt;","synthetic":false,"types":["runwell_entity::secondary::default_bitvec::DefaultComponentBitVec"]},{"text":"impl&lt;K, V&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/secondary/default_map/struct.DefaultComponentMap.html\" title=\"struct runwell_entity::secondary::default_map::DefaultComponentMap\">DefaultComponentMap</a>&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,&nbsp;</span>","synthetic":false,"types":["runwell_entity::secondary::default_map::DefaultComponentMap"]},{"text":"impl&lt;K, V&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/secondary/default_vec/struct.DefaultComponentVec.html\" title=\"struct runwell_entity::secondary::default_vec::DefaultComponentVec\">DefaultComponentVec</a>&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,&nbsp;</span>","synthetic":false,"types":["runwell_entity::secondary::default_vec::DefaultComponentVec"]},{"text":"impl&lt;K, V&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/secondary/map/struct.ComponentMap.html\" title=\"struct runwell_entity::secondary::map::ComponentMap\">ComponentMap</a>&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,&nbsp;</span>","synthetic":false,"types":["runwell_entity::secondary::map::ComponentMap"]},{"text":"impl&lt;K, V&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_entity/secondary/vec/struct.ComponentVec.html\" title=\"struct runwell_entity::secondary::vec::ComponentVec\">ComponentVec</a>&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,&nbsp;</span>","synthetic":false,"types":["runwell_entity::secondary::vec::ComponentVec"]}];
implementors["runwell_ir"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/struct.Indent.html\" title=\"struct runwell_ir::Indent\">Indent</a>","synthetic":false,"types":["runwell_ir::display::Indent"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.CallInstr.html\" title=\"struct runwell_ir::instr::CallInstr\">CallInstr</a>","synthetic":false,"types":["runwell_ir::instruction::call::CallInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.CallIndirectInstr.html\" title=\"struct runwell_ir::instr::CallIndirectInstr\">CallIndirectInstr</a>","synthetic":false,"types":["runwell_ir::instruction::call::CallIndirectInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.ConstInstr.html\" title=\"struct runwell_ir::instr::ConstInstr\">ConstInstr</a>","synthetic":false,"types":["runwell_ir::instruction::constant::ConstInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.ReinterpretInstr.html\" title=\"struct runwell_ir::instr::ReinterpretInstr\">ReinterpretInstr</a>","synthetic":false,"types":["runwell_ir::instruction::conv::ReinterpretInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/operands/enum.BinaryFloatOp.html\" title=\"enum runwell_ir::instr::operands::BinaryFloatOp\">BinaryFloatOp</a>","synthetic":false,"types":["runwell_ir::instruction::float::binary::BinaryFloatOp"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.BinaryFloatInstr.html\" title=\"struct runwell_ir::instr::BinaryFloatInstr\">BinaryFloatInstr</a>","synthetic":false,"types":["runwell_ir::instruction::float::binary::BinaryFloatInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/operands/enum.CompareFloatOp.html\" title=\"enum runwell_ir::instr::operands::CompareFloatOp\">CompareFloatOp</a>","synthetic":false,"types":["runwell_ir::instruction::float::fcmp::CompareFloatOp"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.CompareFloatInstr.html\" title=\"struct runwell_ir::instr::CompareFloatInstr\">CompareFloatInstr</a>","synthetic":false,"types":["runwell_ir::instruction::float::fcmp::CompareFloatInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.DemoteFloatInstr.html\" title=\"struct runwell_ir::instr::DemoteFloatInstr\">DemoteFloatInstr</a>","synthetic":false,"types":["runwell_ir::instruction::float::fconv::DemoteFloatInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.PromoteFloatInstr.html\" title=\"struct runwell_ir::instr::PromoteFloatInstr\">PromoteFloatInstr</a>","synthetic":false,"types":["runwell_ir::instruction::float::fconv::PromoteFloatInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.FloatToIntInstr.html\" title=\"struct runwell_ir::instr::FloatToIntInstr\">FloatToIntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::float::fconv::FloatToIntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/operands/enum.UnaryFloatOp.html\" title=\"enum runwell_ir::instr::operands::UnaryFloatOp\">UnaryFloatOp</a>","synthetic":false,"types":["runwell_ir::instruction::float::unary::UnaryFloatOp"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.UnaryFloatInstr.html\" title=\"struct runwell_ir::instr::UnaryFloatInstr\">UnaryFloatInstr</a>","synthetic":false,"types":["runwell_ir::instruction::float::unary::UnaryFloatInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/enum.FloatInstr.html\" title=\"enum runwell_ir::instr::FloatInstr\">FloatInstr</a>","synthetic":false,"types":["runwell_ir::instruction::float::FloatInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.BinaryIntInstr.html\" title=\"struct runwell_ir::instr::BinaryIntInstr\">BinaryIntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::binary::BinaryIntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/operands/enum.BinaryIntOp.html\" title=\"enum runwell_ir::instr::operands::BinaryIntOp\">BinaryIntOp</a>","synthetic":false,"types":["runwell_ir::instruction::int::binary::BinaryIntOp"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/operands/enum.CompareIntOp.html\" title=\"enum runwell_ir::instr::operands::CompareIntOp\">CompareIntOp</a>","synthetic":false,"types":["runwell_ir::instruction::int::icmp::CompareIntOp"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.CompareIntInstr.html\" title=\"struct runwell_ir::instr::CompareIntInstr\">CompareIntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::icmp::CompareIntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.TruncateIntInstr.html\" title=\"struct runwell_ir::instr::TruncateIntInstr\">TruncateIntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::iconv::TruncateIntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.ExtendIntInstr.html\" title=\"struct runwell_ir::instr::ExtendIntInstr\">ExtendIntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::iconv::ExtendIntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.IntToFloatInstr.html\" title=\"struct runwell_ir::instr::IntToFloatInstr\">IntToFloatInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::iconv::IntToFloatInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.ShiftIntInstr.html\" title=\"struct runwell_ir::instr::ShiftIntInstr\">ShiftIntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::shift::ShiftIntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/operands/enum.ShiftIntOp.html\" title=\"enum runwell_ir::instr::operands::ShiftIntOp\">ShiftIntOp</a>","synthetic":false,"types":["runwell_ir::instruction::int::shift::ShiftIntOp"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/operands/enum.UnaryIntOp.html\" title=\"enum runwell_ir::instr::operands::UnaryIntOp\">UnaryIntOp</a>","synthetic":false,"types":["runwell_ir::instruction::int::unary::UnaryIntOp"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.UnaryIntInstr.html\" title=\"struct runwell_ir::instr::UnaryIntInstr\">UnaryIntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::unary::UnaryIntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/enum.IntInstr.html\" title=\"enum runwell_ir::instr::IntInstr\">IntInstr</a>","synthetic":false,"types":["runwell_ir::instruction::int::IntInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/struct.ImmU64.html\" title=\"struct runwell_ir::ImmU64\">ImmU64</a>","synthetic":false,"types":["runwell_ir::instruction::memory::ImmU64"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.HeapAddrInstr.html\" title=\"struct runwell_ir::instr::HeapAddrInstr\">HeapAddrInstr</a>","synthetic":false,"types":["runwell_ir::instruction::memory::HeapAddrInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.LoadInstr.html\" title=\"struct runwell_ir::instr::LoadInstr\">LoadInstr</a>","synthetic":false,"types":["runwell_ir::instruction::memory::LoadInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.StoreInstr.html\" title=\"struct runwell_ir::instr::StoreInstr\">StoreInstr</a>","synthetic":false,"types":["runwell_ir::instruction::memory::StoreInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.MemoryGrowInstr.html\" title=\"struct runwell_ir::instr::MemoryGrowInstr\">MemoryGrowInstr</a>","synthetic":false,"types":["runwell_ir::instruction::memory::MemoryGrowInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.MemorySizeInstr.html\" title=\"struct runwell_ir::instr::MemorySizeInstr\">MemorySizeInstr</a>","synthetic":false,"types":["runwell_ir::instruction::memory::MemorySizeInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.MatchSelectInstr.html\" title=\"struct runwell_ir::instr::MatchSelectInstr\">MatchSelectInstr</a>","synthetic":false,"types":["runwell_ir::instruction::select::MatchSelectInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/enum.TerminalInstr.html\" title=\"enum runwell_ir::instr::TerminalInstr\">TerminalInstr</a>","synthetic":false,"types":["runwell_ir::instruction::terminal::TerminalInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.ReturnInstr.html\" title=\"struct runwell_ir::instr::ReturnInstr\">ReturnInstr</a>","synthetic":false,"types":["runwell_ir::instruction::terminal::ReturnInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.BranchInstr.html\" title=\"struct runwell_ir::instr::BranchInstr\">BranchInstr</a>","synthetic":false,"types":["runwell_ir::instruction::terminal::BranchInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.TailCallInstr.html\" title=\"struct runwell_ir::instr::TailCallInstr\">TailCallInstr</a>","synthetic":false,"types":["runwell_ir::instruction::terminal::TailCallInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.TailCallIndirectInstr.html\" title=\"struct runwell_ir::instr::TailCallIndirectInstr\">TailCallIndirectInstr</a>","synthetic":false,"types":["runwell_ir::instruction::terminal::TailCallIndirectInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/instr/struct.MatchBranchInstr.html\" title=\"struct runwell_ir::instr::MatchBranchInstr\">MatchBranchInstr</a>","synthetic":false,"types":["runwell_ir::instruction::terminal::MatchBranchInstr"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/instr/enum.Instruction.html\" title=\"enum runwell_ir::instr::Instruction\">Instruction</a>","synthetic":false,"types":["runwell_ir::instruction::Instruction"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/primitive/struct.BlockEntity.html\" title=\"struct runwell_ir::primitive::BlockEntity\">BlockEntity</a>","synthetic":false,"types":["runwell_ir::primitive::BlockEntity"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/primitive/struct.ValueEntity.html\" title=\"struct runwell_ir::primitive::ValueEntity\">ValueEntity</a>","synthetic":false,"types":["runwell_ir::primitive::ValueEntity"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/primitive/enum.Type.html\" title=\"enum runwell_ir::primitive::Type\">Type</a>","synthetic":false,"types":["runwell_ir::primitive::Type"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/primitive/enum.IntType.html\" title=\"enum runwell_ir::primitive::IntType\">IntType</a>","synthetic":false,"types":["runwell_ir::primitive::IntType"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/primitive/enum.FloatType.html\" title=\"enum runwell_ir::primitive::FloatType\">FloatType</a>","synthetic":false,"types":["runwell_ir::primitive::FloatType"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/primitive/enum.Const.html\" title=\"enum runwell_ir::primitive::Const\">Const</a>","synthetic":false,"types":["runwell_ir::primitive::Const"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/primitive/enum.IntConst.html\" title=\"enum runwell_ir::primitive::IntConst\">IntConst</a>","synthetic":false,"types":["runwell_ir::primitive::IntConst"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_ir/primitive/enum.FloatConst.html\" title=\"enum runwell_ir::primitive::FloatConst\">FloatConst</a>","synthetic":false,"types":["runwell_ir::primitive::FloatConst"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/primitive/struct.F32.html\" title=\"struct runwell_ir::primitive::F32\">F32</a>","synthetic":false,"types":["runwell_ir::primitive::F32"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_ir/primitive/struct.F64.html\" title=\"struct runwell_ir::primitive::F64\">F64</a>","synthetic":false,"types":["runwell_ir::primitive::F64"]}];
implementors["runwell_module"] = [{"text":"impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_module/utils/struct.Function.html\" title=\"struct runwell_module::utils::Function\">Function</a>&lt;'a&gt;","synthetic":false,"types":["runwell_module::function::Function"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_module/enum.Mutability.html\" title=\"enum runwell_module::Mutability\">Mutability</a>","synthetic":false,"types":["runwell_module::store::global::Mutability"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_module/struct.GlobalRef.html\" title=\"struct runwell_module::GlobalRef\">GlobalRef</a>","synthetic":false,"types":["runwell_module::store::global::GlobalRef"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_module/utils/struct.Bytes.html\" title=\"struct runwell_module::utils::Bytes\">Bytes</a>","synthetic":false,"types":["runwell_module::store::memory::Bytes"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_module/utils/struct.Pages.html\" title=\"struct runwell_module::utils::Pages\">Pages</a>","synthetic":false,"types":["runwell_module::store::memory::Pages"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"runwell_module/struct.MemoryRef.html\" title=\"struct runwell_module::MemoryRef\">MemoryRef</a>","synthetic":false,"types":["runwell_module::store::memory::MemoryRef"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_module/error/enum.TrapCode.html\" title=\"enum runwell_module::error::TrapCode\">TrapCode</a>","synthetic":false,"types":["runwell_module::store::trap::TrapCode"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"enum\" href=\"runwell_module/enum.RuntimeValue.html\" title=\"enum runwell_module::RuntimeValue\">RuntimeValue</a>","synthetic":false,"types":["runwell_module::store::value::RuntimeValue"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()