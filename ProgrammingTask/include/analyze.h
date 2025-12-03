#ifndef ANALYZE_H
#define ANALYZE_H

#include "ast.h"

/**
 * 语义分析入口函数
 * * 功能：
 * 1. 遍历 AST 进行类型检查 (Type Checking)
 * 2. 标注表达式的类型 (Filling expr->expr_type)
 * 3. 管理作用域与符号表 (Scope Management)
 * 4. 检查语义错误（如变量未声明、重复声明、类型不匹配）
 * * @param stmt AST 的根节点（通常是一个 Statement）
 * * 如果发现错误，该函数通常会打印错误信息并直接调用 exit(1) 终止程序。
 */
void analyze(Stmt *stmt);

#endif