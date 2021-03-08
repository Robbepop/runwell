(function() {var implementors = {};
implementors["runwell_ir"] = [{"text":"impl From&lt;FloatToIntInstr&gt; for FloatInstr","synthetic":false,"types":[]},{"text":"impl From&lt;BinaryFloatInstr&gt; for FloatInstr","synthetic":false,"types":[]},{"text":"impl From&lt;DemoteFloatInstr&gt; for FloatInstr","synthetic":false,"types":[]},{"text":"impl From&lt;CompareFloatInstr&gt; for FloatInstr","synthetic":false,"types":[]},{"text":"impl From&lt;PromoteFloatInstr&gt; for FloatInstr","synthetic":false,"types":[]},{"text":"impl From&lt;UnaryFloatInstr&gt; for FloatInstr","synthetic":false,"types":[]},{"text":"impl From&lt;CompareFloatInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;DemoteFloatInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;PromoteFloatInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;FloatToIntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;UnaryFloatInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;BinaryFloatInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;UnaryIntInstr&gt; for IntInstr","synthetic":false,"types":[]},{"text":"impl From&lt;BinaryIntInstr&gt; for IntInstr","synthetic":false,"types":[]},{"text":"impl From&lt;IntToFloatInstr&gt; for IntInstr","synthetic":false,"types":[]},{"text":"impl From&lt;CompareIntInstr&gt; for IntInstr","synthetic":false,"types":[]},{"text":"impl From&lt;ShiftIntInstr&gt; for IntInstr","synthetic":false,"types":[]},{"text":"impl From&lt;ExtendIntInstr&gt; for IntInstr","synthetic":false,"types":[]},{"text":"impl From&lt;TruncateIntInstr&gt; for IntInstr","synthetic":false,"types":[]},{"text":"impl From&lt;BinaryIntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;UnaryIntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;CompareIntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;TruncateIntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;IntToFloatInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;ExtendIntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;ShiftIntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;u32&gt; for ImmU32","synthetic":false,"types":[]},{"text":"impl From&lt;BranchInstr&gt; for TerminalInstr","synthetic":false,"types":[]},{"text":"impl From&lt;IfThenElseInstr&gt; for TerminalInstr","synthetic":false,"types":[]},{"text":"impl From&lt;ReturnInstr&gt; for TerminalInstr","synthetic":false,"types":[]},{"text":"impl From&lt;TailCallInstr&gt; for TerminalInstr","synthetic":false,"types":[]},{"text":"impl From&lt;()&gt; for TerminalInstr","synthetic":false,"types":[]},{"text":"impl From&lt;TailCallIndirectInstr&gt; for TerminalInstr","synthetic":false,"types":[]},{"text":"impl From&lt;BranchTableInstr&gt; for TerminalInstr","synthetic":false,"types":[]},{"text":"impl From&lt;CallInstr&gt; for TailCallInstr","synthetic":false,"types":[]},{"text":"impl From&lt;CallIndirectInstr&gt; for TailCallIndirectInstr","synthetic":false,"types":[]},{"text":"impl From&lt;ReturnInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;BranchInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;IfThenElseInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;BranchTableInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;TailCallInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;TailCallIndirectInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;LoadInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;MemoryGrowInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;ReinterpretInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;MemorySizeInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;ConstInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;TerminalInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;CallInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;StoreInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;IntInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;CallIndirectInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;HeapAddrInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;SelectInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;FloatInstr&gt; for Instruction","synthetic":false,"types":[]},{"text":"impl From&lt;FloatType&gt; for Type","synthetic":false,"types":[]},{"text":"impl From&lt;()&gt; for Type","synthetic":false,"types":[]},{"text":"impl From&lt;IntType&gt; for Type","synthetic":false,"types":[]},{"text":"impl From&lt;u32&gt; for Const","synthetic":false,"types":[]},{"text":"impl From&lt;IntConst&gt; for Const","synthetic":false,"types":[]},{"text":"impl From&lt;FloatConst&gt; for Const","synthetic":false,"types":[]},{"text":"impl From&lt;f32&gt; for F32","synthetic":false,"types":[]},{"text":"impl From&lt;F32&gt; for Const","synthetic":false,"types":[]},{"text":"impl From&lt;f64&gt; for F64","synthetic":false,"types":[]},{"text":"impl From&lt;F64&gt; for Const","synthetic":false,"types":[]}];
implementors["runwell_module"] = [{"text":"impl From&lt;(ErrorKind, Vec&lt;String, Global&gt;)&gt; for Error","synthetic":false,"types":[]},{"text":"impl From&lt;FunctionBuilderError&gt; for Error","synthetic":false,"types":[]},{"text":"impl From&lt;FunctionBuilderError&gt; for ErrorKind","synthetic":false,"types":[]}];
implementors["runwell_wasm"] = [{"text":"impl&lt;E&gt; From&lt;E&gt; for Error <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;E: Into&lt;ErrorKind&gt;,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl From&lt;TranslateError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;BinaryReaderError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;SectionError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;ReadError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;ExportError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;MemoryError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;String&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;Error&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;ImportError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;InitExprError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;TableError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl From&lt;PrimitiveError&gt; for ErrorKind","synthetic":false,"types":[]},{"text":"impl&lt;'a&gt; From&lt;ImportName&lt;'a&gt;&gt; for ImportName","synthetic":false,"types":[]},{"text":"impl From&lt;Type&gt; for PrimitiveError","synthetic":false,"types":[]},{"text":"impl From&lt;i32&gt; for Const","synthetic":false,"types":[]},{"text":"impl From&lt;i64&gt; for Const","synthetic":false,"types":[]},{"text":"impl From&lt;Ieee32&gt; for Const","synthetic":false,"types":[]},{"text":"impl From&lt;Ieee64&gt; for Const","synthetic":false,"types":[]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()