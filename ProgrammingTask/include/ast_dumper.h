#ifndef AST_DUMPER_H
#define AST_DUMPER_H

#include "ast.h"

/* Dump AST in tree structure format */
void ast_dump_expr(Expr *e, int indent);
void ast_dump_stmt(Stmt *s, int indent);

#endif
