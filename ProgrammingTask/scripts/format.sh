#!/bin/bash
# 代码格式化脚本

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if ! command -v clang-format &> /dev/null; then
    echo "错误: clang-format 未安装"
    exit 1
fi

echo "格式化代码..."
find "$PROJECT_DIR/src" "$PROJECT_DIR/include" "$PROJECT_DIR/tools" \
    -name "*.c" -o -name "*.h" | \
    xargs clang-format -i --style=file

echo "完成!"
