#!/bin/bash
# 生成解析器脚本

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC_DIR="$PROJECT_DIR/src"
BUILD_DIR="$PROJECT_DIR/build"

mkdir -p "$BUILD_DIR"

echo "生成词法分析器..."
flex -o "$BUILD_DIR/lexer.c" "$SRC_DIR/lexer.l"

echo "生成语法分析器..."
bison -d -o "$BUILD_DIR/parser.c" "$SRC_DIR/parser.y"

echo "完成!"
