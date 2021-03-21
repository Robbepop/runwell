(function() {var implementors = {};
implementors["runwell_entity"] = [{"text":"impl UnwindSafe for RawIdx","synthetic":true,"types":[]},{"text":"impl&lt;T:&nbsp;?Sized&gt; UnwindSafe for Idx&lt;T&gt;","synthetic":true,"types":[]},{"text":"impl&lt;T&gt; UnwindSafe for EntityArena&lt;T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: UnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; UnwindSafe for Indices&lt;'a, T&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; UnwindSafe for Entities&lt;'a, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; !UnwindSafe for EntitiesMut&lt;'a, T&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; UnwindSafe for Iter&lt;'a, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; !UnwindSafe for IterMut&lt;'a, T&gt;","synthetic":true,"types":[]},{"text":"impl&lt;T&gt; UnwindSafe for PhantomEntityArena&lt;T&gt;","synthetic":true,"types":[]},{"text":"impl&lt;K&gt; UnwindSafe for DefaultComponentBitVec&lt;K&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K&gt; UnwindSafe for Iter&lt;'a, K&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K&gt; UnwindSafe for Components&lt;'a, K&gt;","synthetic":true,"types":[]},{"text":"impl&lt;K, V&gt; UnwindSafe for DefaultComponentMap&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: UnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; UnwindSafe for Iter&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; UnwindSafe for Components&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;K, V&gt; UnwindSafe for DefaultComponentVec&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: UnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; UnwindSafe for Iter&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; UnwindSafe for Components&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;K, V&gt; UnwindSafe for ComponentMap&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: UnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for Entry&lt;'a, K, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for OccupiedEntry&lt;'a, K, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for VacantEntry&lt;'a, K, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, V&gt; UnwindSafe for Components&lt;'a, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, V&gt; !UnwindSafe for ComponentsMut&lt;'a, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; UnwindSafe for Iter&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for IterMut&lt;'a, K, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;K, V&gt; UnwindSafe for ComponentVec&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: UnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for Entry&lt;'a, K, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for OccupiedEntry&lt;'a, K, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for VacantEntry&lt;'a, K, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, V&gt; UnwindSafe for Components&lt;'a, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, V&gt; !UnwindSafe for ComponentsMut&lt;'a, V&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; UnwindSafe for Iter&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; !UnwindSafe for IterMut&lt;'a, K, V&gt;","synthetic":true,"types":[]}];
implementors["runwell_interpreter"] = [{"text":"impl&lt;'a&gt; UnwindSafe for EvaluationContext&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for InterpretationError","synthetic":true,"types":[]}];
implementors["runwell_ir"] = [{"text":"impl UnwindSafe for Indent","synthetic":true,"types":[]},{"text":"impl UnwindSafe for CallInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for CallIndirectInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ConstInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ReinterpretInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for BinaryFloatOp","synthetic":true,"types":[]},{"text":"impl UnwindSafe for BinaryFloatInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for CompareFloatOp","synthetic":true,"types":[]},{"text":"impl UnwindSafe for CompareFloatInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for DemoteFloatInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for PromoteFloatInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FloatToIntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for UnaryFloatOp","synthetic":true,"types":[]},{"text":"impl UnwindSafe for UnaryFloatInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FloatInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for BinaryIntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for BinaryIntOp","synthetic":true,"types":[]},{"text":"impl UnwindSafe for CompareIntOp","synthetic":true,"types":[]},{"text":"impl UnwindSafe for CompareIntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TruncateIntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ExtendIntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for IntToFloatInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ShiftIntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ShiftIntOp","synthetic":true,"types":[]},{"text":"impl UnwindSafe for UnaryIntOp","synthetic":true,"types":[]},{"text":"impl UnwindSafe for UnaryIntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for IntInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ImmU32","synthetic":true,"types":[]},{"text":"impl UnwindSafe for HeapAddrInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for LoadInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for StoreInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for MemoryGrowInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for MemorySizeInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for MatchSelectInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for MatchSelectInstrBuilder","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for MatchSelectResultsIter&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TerminalInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ReturnInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for BranchInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TailCallInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TailCallIndirectInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for MatchBranchInstr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for MatchBranchInstrBuilder","synthetic":true,"types":[]},{"text":"impl UnwindSafe for Instruction","synthetic":true,"types":[]},{"text":"impl UnwindSafe for EdgeEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FunctionEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FuncTypeEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for LinearMemoryEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TableEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for BlockEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ValueEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for Type","synthetic":true,"types":[]},{"text":"impl UnwindSafe for IntType","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FloatType","synthetic":true,"types":[]},{"text":"impl UnwindSafe for Const","synthetic":true,"types":[]},{"text":"impl UnwindSafe for IntConst","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FloatConst","synthetic":true,"types":[]},{"text":"impl UnwindSafe for F32","synthetic":true,"types":[]},{"text":"impl UnwindSafe for F64","synthetic":true,"types":[]}];
implementors["runwell_module"] = [{"text":"impl UnwindSafe for Error","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ErrorKind","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for FunctionBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FunctionBuilderError","synthetic":true,"types":[]},{"text":"impl&lt;'a, 'b&gt; !UnwindSafe for InstructionBuilder&lt;'a, 'b&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, 'b&gt; !UnwindSafe for MatchSelectInstructionBuilder&lt;'a, 'b&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a, 'b&gt; !UnwindSafe for MatchBranchBuilder&lt;'a, 'b&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FunctionBody","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FunctionType","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FunctionTypeBuilder","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for Function&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for GlobalVariable","synthetic":true,"types":[]},{"text":"impl UnwindSafe for GlobalVariableEntity","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ImportName","synthetic":true,"types":[]},{"text":"impl UnwindSafe for InitExpr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for LinearMemoryDecl","synthetic":true,"types":[]},{"text":"impl UnwindSafe for LinearMemoryInit","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for DataSegmentIter&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleExportsBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleFunctionsBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleFunctionBodiesBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleGlobalsBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleImportsBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleMemoriesBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleMemoryDataBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleTablesBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleTableElementsBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; !UnwindSafe for ModuleTypesBuilder&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ModuleBuilder","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ModuleResources","synthetic":true,"types":[]},{"text":"impl UnwindSafe for Module","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TableDecl","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TableInit","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for ElementSegmentIter&lt;'a&gt;","synthetic":true,"types":[]}];
implementors["runwell_wasm"] = [{"text":"impl UnwindSafe for Error","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ErrorKind","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ExportError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ExportKind","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ExportItem","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for Export&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for FunctionType","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TranslateError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for GlobalVariable","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ImportError","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for ImportName&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for InitExprError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for InitExpr","synthetic":true,"types":[]},{"text":"impl UnwindSafe for MemoryError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for LinearMemoryDecl","synthetic":true,"types":[]},{"text":"impl&lt;'a&gt; UnwindSafe for MemoryDataInit&lt;'a&gt;","synthetic":true,"types":[]},{"text":"impl UnwindSafe for PrimitiveError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for Type","synthetic":true,"types":[]},{"text":"impl UnwindSafe for Const","synthetic":true,"types":[]},{"text":"impl UnwindSafe for ReadError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for SectionError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for UnexpectedWasmPayload","synthetic":true,"types":[]},{"text":"impl UnwindSafe for UnsupportedWasmSection","synthetic":true,"types":[]},{"text":"impl UnwindSafe for UnsupportedTypeDef","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TableError","synthetic":true,"types":[]},{"text":"impl UnwindSafe for TableDecl","synthetic":true,"types":[]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()