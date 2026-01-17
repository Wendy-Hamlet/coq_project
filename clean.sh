#!/bin/bash
# Clean script - removes generated verification files

echo "=== Cleaning Generated Files ==="

cd TheoryTask/qcp-binary-democases/SeparationLogic/examples

echo "Removing generated Coq files (keeping sll_project_lib.v)..."
rm -f sll_project_goal.v \
      sll_project_goal_check.v \
      sll_project_proof_auto.v \
      sll_project_proof_manual.v \
      sll_project_strategy_goal.v \
      sll_project_strategy_goal_check.v \
      sll_project_strategy_proof.v

echo "Removing compiled files..."
rm -f *.vo *.vok *.vos *.glob .*.aux

cd ../../../..

echo "Clean complete!"
