#!/bin/bash
# Copy submission files to SubmissionFiles directory

echo "=== Copying Submission Files ==="

SUBMISSION_DIR="TheoryTask/SubmissionFiles"
QCP_DIR="TheoryTask/qcp-binary-democases"
QCP_EXAMPLES="$QCP_DIR/QCP_examples"
SL_EXAMPLES="$QCP_DIR/SeparationLogic/examples"

# Create directory if not exists
mkdir -p "$SUBMISSION_DIR"

echo "Copying C source files..."
cp "$QCP_EXAMPLES/sll_project_def.h" "$SUBMISSION_DIR/"
cp "$QCP_EXAMPLES/sll_project_lib.c" "$SUBMISSION_DIR/"
cp "$QCP_EXAMPLES/sll_project.strategies" "$SUBMISSION_DIR/"

echo "Copying Coq verification files..."
cp "$SL_EXAMPLES/sll_project_lib.v" "$SUBMISSION_DIR/"
cp "$SL_EXAMPLES/sll_project_goal.v" "$SUBMISSION_DIR/"
cp "$SL_EXAMPLES/sll_project_goal_check.v" "$SUBMISSION_DIR/"
cp "$SL_EXAMPLES/sll_project_proof_auto.v" "$SUBMISSION_DIR/"
cp "$SL_EXAMPLES/sll_project_proof_manual.v" "$SUBMISSION_DIR/"
cp "$SL_EXAMPLES/sll_project_strategy_goal.v" "$SUBMISSION_DIR/"
cp "$SL_EXAMPLES/sll_project_strategy_goal_check.v" "$SUBMISSION_DIR/"
cp "$SL_EXAMPLES/sll_project_strategy_proof.v" "$SUBMISSION_DIR/"

echo "Copy complete! Files are in $SUBMISSION_DIR/"
echo ""
echo "File count:"
ls -1 "$SUBMISSION_DIR" | grep -E '\.(h|c|strategies|v)$' | wc -l
echo "files (expected: 11)"
