#!/bin/bash
# 测试运行脚本

TEST_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$TEST_DIR/.." && pwd)"
BUILD_DIR="$PROJECT_DIR/build"
BIN_DIR="$BUILD_DIR/bin"
CASES_DIR="$TEST_DIR/cases"
EXPECTED_DIR="$TEST_DIR/expected"

# 检查编译产物
if [ ! -f "$BIN_DIR/whiled" ]; then
    echo "错误: 编译产物未找到，请先运行 make 或 cmake --build build"
    exit 1
fi

PASS=0
FAIL=0

echo "运行测试..."
echo "========================================="

# 遍历测试用例
for test_file in "$CASES_DIR"/*.wd; do
    test_name=$(basename "$test_file" .wd)
    expected_file="$EXPECTED_DIR/$test_name.txt"
    
    if [ ! -f "$expected_file" ]; then
        echo "⚠️  跳过: $test_name (预期输出文件不存在)"
        continue
    fi
    
    # 运行编译器
    output=$("$BIN_DIR/whiled" "$test_file" 2>&1)
    expected=$(cat "$expected_file")
    
    # 比较输出
    if [ "$output" = "$expected" ]; then
        echo "✅ 通过: $test_name"
        ((PASS++))
    else
        echo "❌ 失败: $test_name"
        if [ "$1" = "--verbose" ] || [ "$1" = "-v" ]; then
            echo "   预期输出:"
            echo "$expected" | sed 's/^/     /'
            echo "   实际输出:"
            echo "$output" | sed 's/^/     /'
        fi
        ((FAIL++))
    fi
done

echo "========================================="
echo "测试完成: 通过 $PASS, 失败 $FAIL"

if [ $FAIL -eq 0 ]; then
    exit 0
else
    exit 1
fi
