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
    return "ADD";
  case BIN_SUB:
    return "SUB";
  case BIN_MUL:
    return "MUL";
  case BIN_DIV:
    return "DIV";
  case BIN_MOD:
    return "MOD";
  case BIN_EQ:
    return "EQ";
  case BIN_NEQ:
    return "NEQ";
  case BIN_LT:
    return "LT";
  case BIN_GT:
    return "GT";
  case BIN_LE:
    return "LE";
  case BIN_GE:
    return "GE";
  case BIN_AND:
    return "AND";
  case BIN_OR:
    return "OR";
  default:
    return "UNKNOWN_OP";
  }
}

/* Dump an expression in function call form */
void ast_dump_expr(Expr *e, int indent) {
  if (!e) {
    printf("NULL");
    return;
  }

  (void)indent; // Not used for inline function call format

  switch (e->kind) {
  case AST_INT_LITERAL:
    printf("AST_INT_LITERAL(%lld)", e->v.int_val);
    break;

  case AST_VAR:
    printf("AST_VAR(\"%s\")", e->v.var_name);
    break;

  case AST_BINOP:
    printf("AST_BINOP(BIN_%s, ", binop_to_str(e->v.binop.op));
    ast_dump_expr(e->v.binop.lhs, 0);
    printf(", ");
    ast_dump_expr(e->v.binop.rhs, 0);
    printf(")");
    break;

  case AST_UNOP:
    printf("AST_UNOP(");
    ast_dump_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_NOT:
    printf("AST_NOT(");
    ast_dump_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_ADDR:
    printf("AST_ADDR(");
    ast_dump_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_DEREF:
    printf("AST_DEREF(");
    ast_dump_expr(e->v.unop.e, 0);
    printf(")");
    break;

  case AST_CAST:
    printf("AST_CAST(");
    if (e->v.cast.to_type) {
      type_print(e->v.cast.to_type);
    } else {
      printf("TYPE_UNKNOWN");
    }
    printf(", ");
    ast_dump_expr(e->v.cast.e, 0);
    printf(")");
    break;
  }
}

/* Dump a statement in function call form */
void ast_dump_stmt(Stmt *s, int indent) {
  if (!s) {
    printf("NULL");
    return;
  }

  print_indent(indent);
  switch (s->kind) {
  case STMT_SKIP:
    printf("STMT_SKIP()\n");
    break;

  case STMT_SEQ:
    printf("STMT_SEQ(\n");
    ast_dump_stmt(s->v.seq.s1, indent + 1);
    print_indent(indent);
    printf(",\n");
    ast_dump_stmt(s->v.seq.s2, indent + 1);
    print_indent(indent);
    printf(")\n");
    break;

  case STMT_ASSIGN:
    printf("STMT_ASSIGN(\"%s\", ", s->v.assign.lhs);
    ast_dump_expr(s->v.assign.rhs, 0);
    printf(")\n");
    break;

  case STMT_ASSIGN_DEREF:
    printf("STMT_ASSIGN_DEREF(");
    ast_dump_expr(s->v.deref_assign.lhs, 0);
    printf(", ");
    ast_dump_expr(s->v.deref_assign.rhs, 0);
    printf(")\n");
    break;

  case STMT_DECL:
    printf("STMT_DECL(");
    if (s->v.decl.decl_type) {
      type_print(s->v.decl.decl_type);
    } else {
      printf("TYPE_UNKNOWN");
    }
    printf(", \"%s\",\n", s->v.decl.var_name);
    ast_dump_stmt(s->v.decl.body, indent + 1);
    print_indent(indent);
    printf(")\n");
    break;

  case STMT_IF:
    printf("STMT_IF(");
    ast_dump_expr(s->v.ifstmt.cond, 0);
    printf(",\n");
    ast_dump_stmt(s->v.ifstmt.then_branch, indent + 1);
    print_indent(indent);
    printf(",\n");
    ast_dump_stmt(s->v.ifstmt.else_branch, indent + 1);
    print_indent(indent);
    printf(")\n");
    break;

  case STMT_WHILE:
    printf("STMT_WHILE(");
    ast_dump_expr(s->v.whilestmt.cond, 0);
    printf(",\n");
    ast_dump_stmt(s->v.whilestmt.body, indent + 1);
    print_indent(indent);
    printf(")\n");
    break;
  }
}
