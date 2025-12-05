#include "ast.h"
#include "type.h"
#include <stdio.h>

/* Helper to print indentation */
static void print_indent(int indent) {
  for (int i = 0; i < indent; i++) {
    printf("  ");
  }
}

/* Helper to convert binary operator to string */
static const char *binop_to_str(BinOp op) {
  switch (op) {
  case BIN_ADD:
    return "+";
  case BIN_SUB:
    return "-";
  case BIN_MUL:
    return "*";
  case BIN_DIV:
    return "/";
  case BIN_MOD:
    return "%";
  case BIN_EQ:
    return "==";
  case BIN_NEQ:
    return "!=";
  case BIN_LT:
    return "<";
  case BIN_GT:
    return ">";
  case BIN_LE:
    return "<=";
  case BIN_GE:
    return ">=";
  case BIN_AND:
    return "&&";
  case BIN_OR:
    return "||";
  default:
    return "?";
  }
}

/* Print an expression.
 * Note: We print expressions inline (indent is ignored for sub-expressions
 * usually, but passed for consistency if needed later).
 */
void ast_print_expr(Expr *e, int indent) {
  if (!e)
    return;
  (void)indent; // Unused for now for expressions as we print them inline

  switch (e->kind) {
  case AST_INT_LITERAL:
    printf("%lld", e->v.int_val);
    break;

  case AST_VAR:
    printf("%s", e->v.var_name);
    break;

  case AST_BINOP:
    printf("(");
    ast_print_expr(e->v.binop.lhs, 0);
    printf(" %s ", binop_to_str(e->v.binop.op));
    ast_print_expr(e->v.binop.rhs, 0);
    printf(")");
    break;

  case AST_UNOP:
    printf("(-");
    ast_print_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_NOT:
    printf("(!");
    ast_print_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_ADDR:
    printf("(&");
    ast_print_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_DEREF:
    printf("(*");
    ast_print_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_CAST:
    printf("((");
    if (e->v.cast.to_type) {
      type_print(e->v.cast.to_type);
    }
    printf(") ");
    ast_print_expr(e->v.cast.e, 0);
    printf(")");
    break;
  }
}

/* Print a statement with indentation */
void ast_print_stmt(Stmt *s, int indent) {
  if (!s)
    return;

  switch (s->kind) {
  case STMT_SKIP:
    print_indent(indent);
    printf("skip;\n");
    break;

  case STMT_SEQ:
    ast_print_stmt(s->v.seq.s1, indent);
    ast_print_stmt(s->v.seq.s2, indent);
    break;

  case STMT_ASSIGN:
    print_indent(indent);
    printf("%s = ", s->v.assign.lhs);
    ast_print_expr(s->v.assign.rhs, 0);
    printf(";\n");
    break;

  case STMT_ASSIGN_DEREF:
    print_indent(indent);
    printf("*");
    ast_print_expr(s->v.deref_assign.lhs, 0);
    printf(" = ");
    ast_print_expr(s->v.deref_assign.rhs, 0);
    printf(";\n");
    break;

  case STMT_DECL:
    print_indent(indent);
    if (s->v.decl.decl_type) {
      type_print(s->v.decl.decl_type);
    }
    printf(" %s;\n", s->v.decl.var_name);
    // The body of the declaration follows
    ast_print_stmt(s->v.decl.body, indent);
    break;

  case STMT_IF:
    print_indent(indent);
    printf("if (");
    ast_print_expr(s->v.ifstmt.cond, 0);
    printf(") then {\n");
    ast_print_stmt(s->v.ifstmt.then_branch, indent + 1);
    print_indent(indent);
    printf("} else {\n");
    ast_print_stmt(s->v.ifstmt.else_branch, indent + 1);
    print_indent(indent);
    printf("}\n");
    break;

  case STMT_WHILE:
    print_indent(indent);
    printf("while (");
    ast_print_expr(s->v.whilestmt.cond, 0);
    printf(") do {\n");
    ast_print_stmt(s->v.whilestmt.body, indent + 1);
    print_indent(indent);
    printf("}\n");
    break;
  }
}
