#!/bin/bash
# Test runner script for typed WhileD compiler

TEST_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$TEST_DIR/.." && pwd)"
BUILD_DIR="$PROJECT_DIR/build"
BIN_DIR="$BUILD_DIR/bin"
CASES_DIR="$TEST_DIR/cases"
EXPECTED_DIR="$TEST_DIR/expected"

# Check for compiled binaries
if [ ! -f "$BIN_DIR/whiled" ]; then
    echo "Error: Compiled binary not found. Please run 'make' first."
    exit 1
fi

PASS=0
FAIL=0
SKIP=0

echo "Running tests..."
echo "========================================="

# Test valid cases (should compile successfully)
echo ""
echo "--- Valid Test Cases ---"
for test_file in "$CASES_DIR"/test_*.wd; do
    if [ ! -f "$test_file" ]; then
        continue
    fi
    test_name=$(basename "$test_file" .wd)
    
    # Run compiler
    output=$("$BIN_DIR/whiled" "$test_file" 2>&1)
    exit_code=$?
    
    # Valid tests should exit with code 0
    if [ $exit_code -eq 0 ]; then
        echo "✅ PASS: $test_name"
        ((PASS++))
    else
        echo "❌ FAIL: $test_name (expected success, got exit code $exit_code)"
        if [ "$1" = "--verbose" ] || [ "$1" = "-v" ]; then
            echo "   Output:"
            echo "$output" | sed 's/^/     /'
        fi
        ((FAIL++))
    fi
done

# Test error cases (should fail with error)
echo ""
echo "--- Error Test Cases ---"
for test_file in "$CASES_DIR"/err_*.wd; do
    if [ ! -f "$test_file" ]; then
        continue
    fi
    test_name=$(basename "$test_file" .wd)
    
    # Run compiler
    output=$("$BIN_DIR/whiled" "$test_file" 2>&1)
    exit_code=$?
    
    # Error tests should exit with non-zero code
    if [ $exit_code -ne 0 ]; then
        echo "✅ PASS: $test_name (correctly detected error)"
        if [ "$1" = "--verbose" ] || [ "$1" = "-v" ]; then
            echo "   Error message:"
            echo "$output" | sed 's/^/     /'
        fi
        ((PASS++))
    else
        echo "❌ FAIL: $test_name (expected error, but compilation succeeded)"
        ((FAIL++))
    fi
done

echo ""
echo "========================================="
echo "Test Summary: PASS=$PASS, FAIL=$FAIL, SKIP=$SKIP"

if [ $FAIL -eq 0 ]; then
    echo "All tests passed!"
    exit 0
else
    echo "Some tests failed."
    exit 1
fi
