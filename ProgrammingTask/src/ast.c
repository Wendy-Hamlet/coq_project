#include "ast.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"

/* 辅助函数：分配内存 */
static Expr *alloc_expr(ExprKind kind) {
    Expr *e = (Expr *)malloc(sizeof(Expr));
    if (!e) { fprintf(stderr, "Out of memory\n"); exit(1); }
    e->kind = kind;
    e->expr_type = NULL;
    e->cast_to = NULL;
    return e;
}

static Stmt *alloc_stmt(StmtKind kind) {
    Stmt *s = (Stmt *)malloc(sizeof(Stmt));
    if (!s) { fprintf(stderr, "Out of memory\n"); exit(1); }
    s->kind = kind;
    return s;
}

/* 表达式构造函数 */
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

/* 语句构造函数 */
Stmt *ast_skip() {
    return alloc_stmt(STMT_SKIP);
}

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

/* AST 打印工具 (简单实现，用于调试) */
static void print_indent(int indent) {
    for (int i = 0; i < indent; i++) printf("  ");
}

static const char* op_to_str(BinOp op) {
    switch(op) {
        case BIN_ADD: return "+"; case BIN_SUB: return "-";
        case BIN_MUL: return "*"; case BIN_DIV: return "/";
        case BIN_MOD: return "%";
        case BIN_EQ: return "=="; case BIN_NEQ: return "!=";
        case BIN_LT: return "<"; case BIN_GT: return ">";
        case BIN_LE: return "<="; case BIN_GE: return ">=";
        default: return "?";
    }
}

void ast_print_expr(Expr *e, int indent) {
    if (!e) return;
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
            printf(" %s ", op_to_str(e->v.binop.op));
            ast_print_expr(e->v.binop.rhs, 0);
            printf(")");
            break;
        case AST_UNOP:
            printf("(-");
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
            printf("(CAST ");
            ast_print_expr(e->v.cast.e, 0);
            printf(")");
            break;
    }
}

void ast_print_stmt(Stmt *s, int indent) {
    if (!s) return;
    print_indent(indent);
    switch (s->kind) {
        case STMT_SKIP:
            printf("SKIP\n");
            break;
        case STMT_SEQ:
            /* 为了美观，SEQ 不换行打印，而是递归展开 */
            printf("SEQ\n");
            ast_print_stmt(s->v.seq.s1, indent + 1);
            ast_print_stmt(s->v.seq.s2, indent + 1);
            break;
        case STMT_ASSIGN:
            printf("ASSIGN %s := ", s->v.assign.lhs);
            ast_print_expr(s->v.assign.rhs, 0);
            printf("\n");
            break;
        case STMT_DECL:
            printf("DECL %s\n", s->v.decl.var_name);
            ast_print_stmt(s->v.decl.body, indent + 1);
            break;
        case STMT_IF:
            printf("IF ");
            ast_print_expr(s->v.ifstmt.cond, 0);
            printf(" THEN\n");
            ast_print_stmt(s->v.ifstmt.then_branch, indent + 1);
            if (s->v.ifstmt.else_branch) {
                print_indent(indent);
                printf("ELSE\n");
                ast_print_stmt(s->v.ifstmt.else_branch, indent + 1);
            }
            break;
        case STMT_WHILE:
            printf("WHILE ");
            ast_print_expr(s->v.whilestmt.cond, 0);
            printf(" DO\n");
            ast_print_stmt(s->v.whilestmt.body, indent + 1);
            break;
    }
}

/* 释放内存 (可选，暂留空) */
void ast_free_expr(Expr *e) {}
void ast_free_stmt(Stmt *s) {}