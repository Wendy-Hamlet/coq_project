#!/bin/bash
# Build script for TheoryTask Coq verification
# Compatible with Linux, macOS, Cygwin, and WSL

set -e

SKIP_SETUP=false
CLEAN_ONLY=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --skip-setup)
            SKIP_SETUP=true
            shift
            ;;
        --clean-only)
            CLEAN_ONLY=true
            shift
            ;;
        *)
            echo "Unknown option: $1"
            echo "Usage: $0 [--skip-setup] [--clean-only]"
            exit 1
            ;;
    esac
done

echo "=== TheoryTask Build Script ==="

# Detect platform
PLATFORM="linux"
if [[ "$OSTYPE" == "darwin"* ]]; then
    PLATFORM="mac-arm64"
elif [[ "$OSTYPE" == "cygwin" ]] || [[ "$OSTYPE" == "msys" ]]; then
    PLATFORM="win"
fi

BINARY_DIR="${PLATFORM}-binary"
echo "Detected platform: $PLATFORM (using $BINARY_DIR)"

# Step 1: Environment Setup
if [ "$SKIP_SETUP" = false ]; then
    echo -e "\n[1/5] Pulling latest code..."
    git pull || echo "Warning: git pull failed, continuing anyway..."

    echo -e "\n[2/5] Updating submodules..."
    git submodule update --init --recursive

    echo -e "\n[3/5] Building unifysl library..."
    cd TheoryTask/qcp-binary-democases/SeparationLogic/unifysl
    make depend
    make
    cd ../../../..

    echo -e "\n[4/5] Building SeparationLogic library..."
    cd TheoryTask/qcp-binary-democases/SeparationLogic
    make depend
    make
    cd ../../..

    echo -e "\n[5/5] Environment setup complete!"
else
    echo "Skipping environment setup"
fi

if [ "$CLEAN_ONLY" = true ]; then
    echo -e "\nClean-only mode. Exiting."
    exit 0
fi

# Step 2: Generate verification files
echo -e "\n=== Generating Verification Files ==="

cd TheoryTask/qcp-binary-democases

echo "Cleaning old generated files..."
rm -f SeparationLogic/examples/sll_project_goal.v \
      SeparationLogic/examples/sll_project_goal_check.v \
      SeparationLogic/examples/sll_project_proof_auto.v \
      SeparationLogic/examples/sll_project_proof_manual.v \
      SeparationLogic/examples/sll_project_strategy_goal.v \
      SeparationLogic/examples/sll_project_strategy_goal_check.v \
      SeparationLogic/examples/sll_project_strategy_proof.v

echo "Generating C program verification files..."
$BINARY_DIR/symexec.exe \
  --goal-file=SeparationLogic/examples/sll_project_goal.v \
  --proof-auto-file=SeparationLogic/examples/sll_project_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/sll_project_proof_manual.v \
  -I QCP_examples/ \
  -slp QCP_examples/ \
  SimpleC.EE \
  --input-file=QCP_examples/sll_project_lib.c \
  --no-exec-info

echo "Generating strategy verification files..."
$BINARY_DIR/StrategyCheck.exe \
  --strategy-folder-path=SeparationLogic/examples/ \
  --coq-logic-path=SimpleC.EE \
  --input-file=QCP_examples/sll_project.strategies \
  --no-exec-info

echo "Compiling generated Coq files..."
cd SeparationLogic
make depend
make

cd ../../../..

echo -e "\n=== Build Complete ==="
echo "All verification files have been generated and compiled."

# Copy submission files
echo ""
echo "Copying files to TheoryTask/SubmissionFiles/..."
./copy_submission_files.sh
