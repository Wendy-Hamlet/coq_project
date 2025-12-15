CURRENT_DIR=.
SETS_DIR = sets
COMPCERT_DIR = compcert_lib
PL_DIR = pl
ASSIGNMENT_DIR = MergableList
QCP_DIR = qcp-binary-democases/SeparationLogic

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

PL_FLAG = -R $(PL_DIR) PL -R $(ASSIGNMENT_DIR) PL.Assignment

SETS_FLAG = -R $(SETS_DIR) SetsClass

COMPCERT_FLAG = -R $(COMPCERT_DIR) compcert.lib

QCP_FLAG = -R $(QCP_DIR)/SeparationLogic SimpleC.SL -R $(QCP_DIR)/unifysl Logic -R $(QCP_DIR)/sets SetsClass -R $(QCP_DIR)/compcert_lib compcert.lib -R $(QCP_DIR)/auxlibs AUXLib -R $(QCP_DIR)/examples SimpleC.EE -R $(QCP_DIR)/StrategyLib SimpleC.StrategyLib -R $(QCP_DIR)/Common SimpleC.Common -R $(QCP_DIR)/fixedpoints FP -R $(QCP_DIR)/MonadLib MonadLib

DEP_FLAG = -R $(PL_DIR) PL -R $(ASSIGNMENT_DIR) PL.Assignment -R $(QCP_DIR)/SeparationLogic SimpleC.SL -R $(QCP_DIR)/unifysl Logic -R $(QCP_DIR)/sets SetsClass -R $(QCP_DIR)/compcert_lib compcert.lib -R $(QCP_DIR)/auxlibs AUXLib -R $(QCP_DIR)/examples SimpleC.EE -R $(QCP_DIR)/StrategyLib SimpleC.StrategyLib -R $(QCP_DIR)/Common SimpleC.Common -R $(QCP_DIR)/fixedpoints FP -R $(QCP_DIR)/MonadLib MonadLib

SETS_FILE_NAMES = \
   Test.v SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v
   
SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)
   
COMPCERT_FILE_NAMES = \
    Coqlib.v Integers.v Zbits.v
    
COMPCERT_FILES=$(COMPCERT_FILE_NAMES:%.v=$(COMPCERT_DIR)/%.v)

PL_FILE_NAMES = \
	MonadHoare.v FixedPoint.v Monad.v  Kleene.v Syntax.v SimpleProofsAndDefs.v HighOrder.v SimpleInductiveType.v AlgebraicStructure.v Rewrite.v DenotationsOfExpr.v DenotationsAsRels.v Sets.v Logic.v MoreInductiveType.v Sets2.v BuiltInNat.v 
PL_FILES=$(PL_FILE_NAMES:%.v=$(PL_DIR)/%.v)

ASSIGNMENT_FILE_NAMES = \
	

ASSIGNMENT_FILES=$(ASSIGNMENT_FILE_NAMES:%.v=$(ASSIGNMENT_DIR)/%.v)

FILES = $(PL_FILES) \
	$(ASSIGNMENT_FILES) \
#   $(SETS_FILES) \
  $(COMPCERT_FILES) \

$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<;
	@$(COQC) $(SETS_FLAG) $<

$(COMPCERT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<;
	@$(COQC) $(COMPCERT_FLAG) $<
			
$(PL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F);
	@$(COQC) $(PL_FLAG) $(QCP_FLAG) $<

$(ASSIGNMENT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F);
	@$(COQC) $(PL_FLAG) $(QCP_FLAG) $<

all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob;
	@rm -f *.vo */*.vo;
	@rm -f *.vok */*.vok;
	@rm -f *.vos */*.vos; 
	@rm -f .*.aux */.*.aux;
	@rm -f .depend;

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend