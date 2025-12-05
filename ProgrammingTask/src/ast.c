#include "ast.h"
#include "util.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Helper function: allocate memory for expression */
static Expr *alloc_expr(ExprKind kind) {
  Expr *e = (Expr *)malloc(sizeof(Expr));
  if (!e) {
    fprintf(stderr, "Out of memory\n");
    exit(1);
  }
  e->kind = kind;
  e->expr_type = NULL;
  e->cast_to = NULL;
  return e;
}

static Stmt *alloc_stmt(StmtKind kind) {
  Stmt *s = (Stmt *)malloc(sizeof(Stmt));
  if (!s) {
    fprintf(stderr, "Out of memory\n");
    exit(1);
  }
  s->kind = kind;
  return s;
}

/* Expression constructors */
Expr *ast_int_literal(long long v) {
  Expr *e = alloc_expr(AST_INT_LITERAL);
  e->v.int_val = v;
  return e;
}

Expr *ast_var(const char *name) {
  Expr *e = alloc_expr(AST_VAR);
  e->v.var_name = xstrdup(name);
  return e;
}

Expr *ast_binop(BinOp op, Expr *l, Expr *r) {
  Expr *e = alloc_expr(AST_BINOP);
  e->v.binop.op = op;
  e->v.binop.lhs = l;
  e->v.binop.rhs = r;
  return e;
}

Expr *ast_unop(Expr *sub) {
  Expr *e = alloc_expr(AST_UNOP);
  e->v.unop.e = sub;
  return e;
}

Expr *ast_not(Expr *sub) {
  Expr *e = alloc_expr(AST_NOT);
  e->v.unop.e = sub;
  return e;
}

Expr *ast_addr(Expr *sub) {
  Expr *e = alloc_expr(AST_ADDR);
  e->v.unop.e = sub;
  return e;
}

Expr *ast_deref(Expr *sub) {
  Expr *e = alloc_expr(AST_DEREF);
  e->v.unop.e = sub;
  return e;
}

Expr *ast_cast(Type *t, Expr *sub) {
  Expr *e = alloc_expr(AST_CAST);
  e->v.cast.to_type = t;
  e->v.cast.e = sub;
  return e;
}

/* Statement constructors */
Stmt *ast_skip() { return alloc_stmt(STMT_SKIP); }

Stmt *ast_seq(Stmt *s1, Stmt *s2) {
  Stmt *s = alloc_stmt(STMT_SEQ);
  s->v.seq.s1 = s1;
  s->v.seq.s2 = s2;
  return s;
}

Stmt *ast_assign(const char *lhs, Expr *rhs) {
  Stmt *s = alloc_stmt(STMT_ASSIGN);
  s->v.assign.lhs = xstrdup(lhs);
  s->v.assign.rhs = rhs;
  return s;
}

Stmt *ast_assign_deref(Expr *lhs, Expr *rhs) {
  Stmt *s = alloc_stmt(STMT_ASSIGN_DEREF);
  s->v.deref_assign.lhs = lhs;
  s->v.deref_assign.rhs = rhs;
  return s;
}

Stmt *ast_decl(Type *t, const char *var, Stmt *body) {
  Stmt *s = alloc_stmt(STMT_DECL);
  s->v.decl.decl_type = t;
  s->v.decl.var_name = xstrdup(var);
  s->v.decl.body = body;
  return s;
}

Stmt *ast_if(Expr *c, Stmt *t, Stmt *e) {
  Stmt *s = alloc_stmt(STMT_IF);
  s->v.ifstmt.cond = c;
  s->v.ifstmt.then_branch = t;
  s->v.ifstmt.else_branch = e;
  return s;
}

Stmt *ast_while(Expr *c, Stmt *body) {
  Stmt *s = alloc_stmt(STMT_WHILE);
  s->v.whilestmt.cond = c;
  s->v.whilestmt.body = body;
  return s;
}

/* AST printing utilities have been moved to ast_printer.c */

/* Memory deallocation (optional, left empty for now) */
void ast_free_expr(Expr *e) { (void)e; }
void ast_free_stmt(Stmt *s) { (void)s; }