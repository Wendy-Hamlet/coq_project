#!/bin/bash
# run_examples.sh - Run all example WhileD programs
# Usage: ./tests/run_examples.sh

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get script directory and project root
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
WHILED="$PROJECT_ROOT/build/bin/whiled"
EXAMPLES_DIR="$PROJECT_ROOT/examples"

echo "========================================"
echo "  WhileD Example Programs Runner"
echo "========================================"
echo ""

# Check if compiler exists
if [ ! -f "$WHILED" ]; then
    echo -e "${RED}Error: Compiler not found at $WHILED${NC}"
    echo "Please run 'make' first to build the compiler."
    exit 1
fi

# Count statistics
total=0
passed=0
failed=0

# Run each example file
for example in "$EXAMPLES_DIR"/*.wd; do
    if [ -f "$example" ]; then
        filename=$(basename "$example")
        total=$((total + 1))
        
        echo -n "Testing $filename ... "
        
        # Check if file is empty
        if [ ! -s "$example" ]; then
            echo -e "${YELLOW}SKIPPED (empty file)${NC}"
            continue
        fi
        
        # Run the compiler
        if "$WHILED" "$example" 2>&1; then
            echo -e "${GREEN}PASSED${NC}"
            passed=$((passed + 1))
        else
            echo -e "${RED}FAILED${NC}"
            failed=$((failed + 1))
        fi
    fi
done

echo ""
echo "========================================"
echo "  Results: $passed/$total passed"
if [ $failed -gt 0 ]; then
    echo -e "  ${RED}$failed tests failed${NC}"
    exit 1
else
    echo -e "  ${GREEN}All tests passed!${NC}"
fi
echo "========================================"
