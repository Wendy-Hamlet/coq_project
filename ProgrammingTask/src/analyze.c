#include "analyze.h"
#include "symtab.h"
#include "type.h"
#include "ast.h"
#include <stdio.h>
#include <stdlib.h>

/* * 全局状态：当前符号表作用域
 * symtab.c 提供了 push/pop 接口，我们在这里维护栈顶指针
 */
static SymTab *current_scope = NULL;

/* 错误处理辅助函数 */
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

/* 前向声明 */
static void check_stmt(Stmt *s);
static void check_expr(Expr *e);

/* * ============================================
 * 表达式分析 (Expression Analysis)
 * 核心任务：标注类型 (e->expr_type)，检查类型兼容性
 * ============================================
 */
static void check_expr(Expr *e) {
    if (!e) return;

    switch (e->kind) {
        case AST_INT_LITERAL:
            e->expr_type = type_make_basic(TYPE_LLONG);
            break;

        case AST_VAR: {
            // 核心改变：使用 current_scope 进行查找
            Symbol *s = symtab_lookup(current_scope, e->v.var_name);
            if (!s) {
                error_undefined_var(e->v.var_name);
            }
            // 符号表返回的是 Symbol结构体，我们需要里面的 type
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
                    // 比较运算：左右操作数必须兼容
                    if (!type_can_convert(l, r) && !type_can_convert(r, l)) {
                        fprintf(stderr, "Error: Cannot compare incompatible types\n");
                        exit(1);
                    }
                    e->expr_type = type_make_basic(TYPE_INT); // 布尔结果
                    break;
                
                default: // 加减乘除模
                    // 这里可以扩展指针算术逻辑 (如 int* + int)
                    // 目前简化为：必须找到公共类型
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

/* * ============================================
 * 语句分析 (Statement Analysis)
 * 核心任务：作用域管理 (push/pop)，控制流检查
 * ============================================
 */
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
            // 赋值：检查左值是否存在，右值类型是否匹配
            Symbol *sym = symtab_lookup(current_scope, s->v.assign.lhs);
            if (!sym) {
                error_undefined_var(s->v.assign.lhs);
            }
            
            check_expr(s->v.assign.rhs);
            
            // 检查 rhs 是否可以转换为 lhs 的类型
            if (!type_can_convert(s->v.assign.rhs->expr_type, sym->type)) {
                fprintf(stderr, "Error: Cannot assign type to variable '%s'\n", s->v.assign.lhs);
                error("Type mismatch in assignment");
            }
            break;
        }

        case STMT_DECL: {
            /* * 关键逻辑：AST_DECL 结构是 (Type, Name, Body)
             * 这意味着变量只在 Body 内部有效 (Let-binding 风格)
             */
            
            // 1. 进入新作用域
            current_scope = symtab_push(current_scope);

            // 2. 在当前作用域插入新变量
            // 注意：symtab_insert 会检查当前层级是否有重复
            bool success = symtab_insert(current_scope, s->v.decl.var_name, s->v.decl.decl_type);
            if (!success) {
                error_redefined_var(s->v.decl.var_name);
            }

            // 3. 递归分析 Body (变量在 Body 中可见)
            check_stmt(s->v.decl.body);

            // 4. 退出作用域 (变量销毁)
            current_scope = symtab_pop(current_scope);
            break;
        }

        case STMT_IF:
            check_expr(s->v.ifstmt.cond);
            // 简单检查：条件必须是整数类型 (C 语言风格，非0即真)
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

/* * ============================================
 * 语义分析入口
 * ============================================
 */
void analyze(Stmt *stmt) {
    // 1. 初始化全局作用域 (Global Scope)
    // 根据 symtab.c，symtab_push(NULL) 创建根表
    current_scope = symtab_push(NULL);

    // 2. 开始递归分析 AST
    check_stmt(stmt);

    // 3. 清理全局作用域
    // 实际编译器可能保留它用于后续代码生成，但在 analyze 结束时弹出是好习惯
    current_scope = symtab_pop(current_scope);
    
    if (current_scope != NULL) {
        fprintf(stderr, "Warning: Symbol table stack not empty after analysis\n");
    }
}