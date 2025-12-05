#ifndef ANALYZE_H
#define ANALYZE_H

#include "ast.h"

/**
 * Semantic analysis entry function.
 *
 * Functionality:
 * 1. Traverse the AST to perform type checking
 * 2. Annotate expressions with their types (filling expr->expr_type)
 * 3. Manage scopes and symbol table
 * 4. Check semantic errors (undefined variables, redefinitions, type mismatches)
 *
 * @param stmt The root node of the AST (typically a Statement)
 *
 * On error, this function prints an error message and calls exit(1) to terminate.
 */
void analyze(Stmt *stmt);

#endif