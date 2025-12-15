CURRENT_DIR=.
COQBIN=

-include CONFIGURE

# Platform-specific settings
ifeq ($(shell uname),Darwin)
	DATE = gdate
else
	DATE = date
endif

# Timing utility
timeit = @printf "%-70s" $(1); t0=$$($(DATE) +%s%3N); $(2); t1=$$($(DATE) +%s%3N); echo "$$((t1 - t0)) ms"

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	Common auxlibs compcert_lib SeparationLogic sets unifysl StrategyLib fixedpoints MonadLib examples
 
COQ_FLAG = -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib

DEP_FLAG = -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib

Common_FILES = \
  CTypes.v COps.v Notations.v

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v List_lemma.v relations.v ListLib.v \
  OrdersDecFact.v BinaryTree.v EqDec.v ListDec.v Bool.v Tactics.v Vec.v

Sets_FILES = \
  SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v

Unify_FILES = \
   Interface.v 

FIXPOINT_FILES = \
  Coqlib.v LiftConstructors.v  PartialOrder_Setoid.v  KnasterTarski.v  BourbakiWitt.v AllFramework.v SetsFixedpoints.v

ListMonad_Files = \
	 ListMonad.v ListBasic.v

OptionMonad_Files = \
	 OptionMonad.v OptionBasic.v

SetMonad_Files = \
	SetBasic.v SetHoare.v FixpointLib.v SetMonad.v

StateRelMonad_Files = \
	StateRelBasic.v StateRelHoare.v FixpointLib.v safeexec_lib.v StateRelMonad.v

MonadErr_Files = \
	MonadErrBasic.v MonadErrLoop.v MonadErrHoare.v monadesafe_lib.v StateRelMonadErr.v

MonadExample_FILES = \
	kmp.v mergesort.v 
  
MONAD_FILES = \
	MonadLib/MonadLib.v \
	MonadLib/Monad.v \
	$(ListMonad_Files:%.v=MonadLib/ListMonad/%.v) \
	$(OptionMonad_Files:%.v=MonadLib/OptionMonad/%.v) \
	$(SetMonad_Files:%.v=MonadLib/SetMonad/%.v) \
	$(StateRelMonad_Files:%.v=MonadLib/StateRelMonad/%.v) \
	$(MonadErr_Files:%.v=MonadLib/MonadErr/%.v) \
	$(MonadExample_FILES:%.v=MonadLib/Examples/%.v) \

SL_FILES = \
  CommonAssertion.v Assertion.v Mem.v ConAssertion.v \
  NestedCriticalSTS.v CriticalSTS.v \
  IntLib.v ArrayLib.v StoreAux.v pocv02.v SeparationLogic.v CNotation.v

StrategyLib_FILES = \
  DepList.v Mapping.v

Examples_Lib_FILES = \
	poly_sll_lib.v sll_lib.v sll_merge_lib.v sll_insert_sort_lib.v functional_queue_lib.v dll_queue_lib.v \
	sll_queue_lib.v simple_arith/Apos_lib.v simple_arith/PDiv_lib.v bst_lib.v bst_fp_lib.v swap_lib.v \
	eval_lib.v   avl_shape.v sll_shape_lib.v dll_shape_lib.v \
	sll_merge_rel_lib.v kmp_lib.v kmp_rel_lib.v int_array_merge_rel_lib.v \
	malloc.v super_poly_sll2.v  

Examples_FILE_NAME = \
	poly_sll sll  sll_insert_sort functional_queue   simple_arith/abs \
	simple_arith/add  simple_arith/gcd simple_arith/Always_pos simple_arith/div_test \
	simple_arith/exgcd sum bst_insert bst_insert_rec bst_fp_delete swap eval bst_delete_rec \
	bst_delete_rec2  avl_insert sll_auto dll_auto array_auto chars \
	kmp_rel int_array_merge_rel sll_merge_rel sll_split_while 

Examples_FILES = \
	$(addsuffix _goal.v, $(Examples_FILE_NAME)) \
	$(addsuffix _goal_check.v, $(Examples_FILE_NAME)) \
	$(addsuffix _proof_auto.v, $(Examples_FILE_NAME)) \
	$(addsuffix _proof_manual.v, $(Examples_FILE_NAME)) \
	$(Examples_Lib_FILES)

Strategy_FILE_NAME = \
	common poly_sll sll_shape sll dll_queue functional_queue sll_queue int_array undef_uint_array\
	 uint_array array_shape bst bst_fp eval char_array  avl dll_shape safeexec safeexecE
  
StrategyProof_FILES = \
	$(addsuffix _strategy_goal.v, $(Strategy_FILE_NAME)) \
	$(addsuffix _strategy_goal_check.v, $(Strategy_FILE_NAME)) \
	$(addsuffix _strategy_proof.v, $(Strategy_FILE_NAME)) \

LiteOS_Lib_FILES = \
	dll sortlink tick_backup glob_vars_and_defs tick Los_Verify_State_def

LiteOS_FILE_NAME = \
	Get_Set_Value GetSortLinkNextExpireTime List_Add LOS_ListDelete LOS_ListDelInit LOS_ListEmpty LOS_ListInit OsAdd2SortLink OsDeleteNodeSortLink \
	OsDeleteSortLink OsGetNextExpireTime OsGetSortLinkAttribute OsSortLinkGetNextExpireTime OsSortLinkGetRemainTime OsSortLinkGetTargetExpireTime \
	OsSortLinkInit OsSortLinkResponseTimeConvertFreq

LiteOS_Strategy_FILE_NAME = \
	los_sortlink



EXAMPLE = \
	$(SL_FILES:%.v=SeparationLogic/%.v) \
	$(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
	$(Common_FILES:%.v=Common/%.v) \
	$(MONAD_FILES:%.v=%.v) \
	$(Sets_FILES:%.v=sets/%.v) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.v) \
	$(Examples_FILES:%.v=examples/%.v) \
	$(StrategyProof_FILES:%.v=examples/%.v) \
	$(Compcertlib_FILES:%.v=compcert_lib/%.v) \
	$(Auxlibs_FILES:%.v=auxlibs/%.v) 

$(EXAMPLE:%.v=%.vo): %.vo: %.v
ifeq ($(TIMING),)
	@echo "COQC $*.v"
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v
else
	$(call timeit, "COQC $*.v", $(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v)
endif

	

all: \
	$(EXAMPLE:%.v=%.vo) \

examples : \
	$(EXAMPLE:%.v=%.vo) 

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(EXAMPLE)  > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(EXAMPLE) > .depend

clean:
	@rm -f $(EXAMPLE:%.v=%.glob)
	@rm -f $(EXAMPLE:%.v=%.vo)
	@rm -f $(EXAMPLE:%.v=%.vok)
	@rm -f $(EXAMPLE:%.v=%.vos)
	@rm -f **/.*.aux
	@rm -f examples/**/.*.aux examples/LiteOS/lib/.*.aux
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

include .depend