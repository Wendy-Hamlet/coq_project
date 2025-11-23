#ifndef AST_H
#define AST_H

#include "type.h"
#include <stdbool.h>

typedef enum {
    AST_INT_LITERAL,
    AST_VAR,
    AST_BINOP,
    AST_UNOP,      // unary minus
    AST_CAST,
    AST_ADDR,      // address-of (&)
    AST_DEREF      // dereference (*)
} ExprKind;

typedef enum {
    BIN_ADD,
    BIN_SUB,
    BIN_MUL,
    BIN_DIV,
    BIN_MOD,    // modulo operator
    BIN_EQ,
    BIN_NEQ,
    BIN_LT,
    BIN_GT,
    BIN_LE,
    BIN_GE
} BinOp;

/* Forward declarations */
struct Expr;
struct Stmt;

/* Expression node */
typedef struct Expr {
    ExprKind kind;

    Type *expr_type;      // type after inference
    Type *cast_to;        // used only after implicit conversion phase; may be NULL

    union {
        long long int_val;

        /* variable */
        const char *var_name;

        /* unary operation */
        struct {
            struct Expr *e;
        } unop;

        /* binary operation */
        struct {
            BinOp op;
            struct Expr *lhs;
            struct Expr *rhs;
        } binop;

        /* (T) e cast */
        struct {
            Type *to_type;
            struct Expr *e;
        } cast;
    } v;
} Expr;

/* Statement kinds */
typedef enum {
    STMT_SKIP,
    STMT_SEQ,
    STMT_ASSIGN,
    STMT_DECL,
    STMT_IF,
    STMT_WHILE
} StmtKind;

/* Statement node */
typedef struct Stmt {
    StmtKind kind;

    union {
        /* seq: s1; s2 */
        struct { struct Stmt *s1, *s2; } seq;

        /* x = e */
        struct {
            const char *lhs;
            Expr *rhs;
        } assign;

        /* type x; body */
        struct {
            Type *decl_type;
            const char *var_name;
            struct Stmt *body;
        } decl;

        /* if (cond) then s1 else s2 */
        struct {
            Expr *cond;
            struct Stmt *then_branch;
            struct Stmt *else_branch;
        } ifstmt;

        /* while (cond) do body */
        struct {
            Expr *cond;
            struct Stmt *body;
        } whilestmt;
    } v;
} Stmt;

/* Summary: constructors */
Expr *ast_int_literal(long long v);
Expr *ast_var(const char *name);
Expr *ast_binop(BinOp op, Expr *l, Expr *r);
Expr *ast_unop(Expr *e);                     // unary minus
Expr *ast_addr(Expr *e);                     // address-of (&)
Expr *ast_deref(Expr *e);                    // dereference (*)
Expr *ast_cast(Type *t, Expr *e);

Stmt *ast_skip();
Stmt *ast_seq(Stmt *s1, Stmt *s2);
Stmt *ast_assign(const char *lhs, Expr *rhs);
Stmt *ast_decl(Type *t, const char *var, Stmt *body);
Stmt *ast_if(Expr *c, Stmt *t, Stmt *e);
Stmt *ast_while(Expr *c, Stmt *body);

/* Memory deallocation */
void ast_free_expr(Expr *e);
void ast_free_stmt(Stmt *s);

/* Pretty printing utilities */
void ast_print_expr(Expr *e, int indent);
void ast_print_stmt(Stmt *s, int indent);

#endif
