#include "analyze.h"
#include "symtab.h"
#include "type.h"
#include "ast.h"
#include <stdio.h>
#include <stdlib.h>

static SymTab *current_scope = NULL;

static void error(const char *msg) {
    fprintf(stderr, "Semantic Error: %s\n", msg);
    exit(1);
}

static void error_undefined_var(const char *name) {
    fprintf(stderr, "Semantic Error: Undefined variable '%s'\n", name);
    exit(1);
}

static void error_redefined_var(const char *name) {
    fprintf(stderr, "Semantic Error: Redefinition of variable '%s' in the same scope\n", name);
    exit(1);
}

static void check_stmt(Stmt *s);
static void check_expr(Expr *e);


static void check_expr(Expr *e) {
    if (!e) return;

    switch (e->kind) {
        case AST_INT_LITERAL:
            e->expr_type = type_make_basic(TYPE_LLONG);
            break;

        case AST_VAR: {
            Symbol *s = symtab_lookup(current_scope, e->v.var_name);
            if (!s) {
                error_undefined_var(e->v.var_name);
            }
            e->expr_type = s->type; 
            break;
        }

        case AST_BINOP: {
            check_expr(e->v.binop.lhs);
            check_expr(e->v.binop.rhs);
            
            Type *l = e->v.binop.lhs->expr_type;
            Type *r = e->v.binop.rhs->expr_type;

            switch (e->v.binop.op) {
                case BIN_EQ: case BIN_NEQ:
                case BIN_LT: case BIN_GT:
                case BIN_LE: case BIN_GE:
                    if (!type_can_convert(l, r) && !type_can_convert(r, l)) {
                        fprintf(stderr, "Error: Cannot compare incompatible types\n");
                        exit(1);
                    }
                    e->expr_type = type_make_basic(TYPE_INT); 
                    break;
                
                default: 
                    e->expr_type = type_common(l, r);
                    if (e->expr_type->kind == TYPE_ERROR) {
                        fprintf(stderr, "Error: Incompatible types in arithmetic operation\n");
                        exit(1);
                    }
                    break;
            }
            break;
        }

        case AST_UNOP:
            check_expr(e->v.unop.e);
            if (!type_is_integer(e->v.unop.e->expr_type)) {
                error("Unary '-' requires integer operand");
            }
            e->expr_type = e->v.unop.e->expr_type;
            break;

        case AST_ADDR: // &x
            check_expr(e->v.unop.e);
            if (e->v.unop.e->kind != AST_VAR && e->v.unop.e->kind != AST_DEREF) {
                error("Cannot take address of rvalue (need a variable or dereference)");
            }
            e->expr_type = type_make_ptr(e->v.unop.e->expr_type);
            break;

        case AST_DEREF: // *x
            check_expr(e->v.unop.e);
            if (!type_is_pointer(e->v.unop.e->expr_type)) {
                error("Cannot dereference non-pointer type");
            }
            e->expr_type = e->v.unop.e->expr_type->base;
            break;

        case AST_CAST:
            check_expr(e->v.cast.e);
            if (!type_can_convert(e->v.cast.e->expr_type, e->v.cast.to_type)) {
                // 警告但不报错，强制转换通常是允许的
                // fprintf(stderr, "Warning: Explicit cast between incompatible types\n");
            }
            e->expr_type = e->v.cast.to_type;
            break;
    }
}

static void check_stmt(Stmt *s) {
    if (!s) return;

    switch (s->kind) {
        case STMT_SKIP:
            break;

        case STMT_SEQ:
            check_stmt(s->v.seq.s1);
            check_stmt(s->v.seq.s2);
            break;

        case STMT_ASSIGN: {
            Symbol *sym = symtab_lookup(current_scope, s->v.assign.lhs);
            if (!sym) {
                error_undefined_var(s->v.assign.lhs);
            }
            
            check_expr(s->v.assign.rhs);
            
            if (!type_can_convert(s->v.assign.rhs->expr_type, sym->type)) {
                fprintf(stderr, "Error: Cannot assign type to variable '%s'\n", s->v.assign.lhs);
                error("Type mismatch in assignment");
            }
            break;
        }

        case STMT_DECL: {
            current_scope = symtab_push(current_scope);

            bool success = symtab_insert(current_scope, s->v.decl.var_name, s->v.decl.decl_type);
            if (!success) {
                error_redefined_var(s->v.decl.var_name);
            }

            check_stmt(s->v.decl.body);

            current_scope = symtab_pop(current_scope);
            break;
        }

        case STMT_IF:
            check_expr(s->v.ifstmt.cond);
            if (!type_is_integer(s->v.ifstmt.cond->expr_type)) {
                error("IF condition must be an integer/boolean type");
            }
            check_stmt(s->v.ifstmt.then_branch);
            if (s->v.ifstmt.else_branch) {
                check_stmt(s->v.ifstmt.else_branch);
            }
            break;

        case STMT_WHILE:
            check_expr(s->v.whilestmt.cond);
            if (!type_is_integer(s->v.whilestmt.cond->expr_type)) {
                error("WHILE condition must be an integer/boolean type");
            }
            check_stmt(s->v.whilestmt.body);
            break;
    }
}

void analyze(Stmt *stmt) {

    current_scope = symtab_push(NULL);

    check_stmt(stmt);

    current_scope = symtab_pop(current_scope);
    
    if (current_scope != NULL) {
        fprintf(stderr, "Warning: Symbol table stack not empty after analysis\n");
    }
}