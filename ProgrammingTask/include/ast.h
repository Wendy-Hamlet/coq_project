#ifndef AST_H
#define AST_H

#include <stddef.h>

/**
 * 抽象语法树节点类型
 */
typedef enum {
    // 表达式
    AST_NUMBER,          // 数字常量
    AST_IDENT,           // 标识符
    AST_BINOP,           // 二元操作
    AST_UNOP,            // 一元操作
    AST_CAST,            // 类型转换
    AST_DEREF,           // 解引用
    AST_ADDRESS,         // 取地址

    // 语句
    AST_ASSIGN,          // 赋值
    AST_DECL,            // 变量声明
    AST_WHILE,           // While 循环
    AST_IF,              // If-Then-Else
    AST_SEQ,             // 语句序列
    AST_SKIP,            // Skip
    
    // 程序
    AST_PROGRAM          // 程序
} ast_node_type_t;

/**
 * 二元操作符
 */
typedef enum {
    BINOP_PLUS,
    BINOP_MINUS,
    BINOP_MULT,
    BINOP_DIV,
    BINOP_MOD,
    BINOP_EQ,
    BINOP_NEQ,
    BINOP_LT,
    BINOP_LTE,
    BINOP_GT,
    BINOP_GTE,
    BINOP_AND,
    BINOP_OR
} binop_t;

/**
 * 一元操作符
 */
typedef enum {
    UNOP_NEG,            // 负号
    UNOP_NOT             // 逻辑非
} unop_t;

/**
 * AST 节点
 */
typedef struct ast_node {
    ast_node_type_t type;
    int line;            // 源代码行号
    int column;          // 源代码列号
    
    union {
        // AST_NUMBER
        struct {
            long value;
        } number;
        
        // AST_IDENT
        struct {
            char* name;
        } ident;
        
        // AST_BINOP
        struct {
            binop_t op;
            struct ast_node* left;
            struct ast_node* right;
        } binop;
        
        // AST_UNOP
        struct {
            unop_t op;
            struct ast_node* operand;
        } unop;
        
        // AST_CAST
        struct {
            struct ast_node* expr;
            // type 在语义分析阶段填充
        } cast;
        
        // AST_DEREF, AST_ADDRESS
        struct {
            struct ast_node* expr;
        } unary_expr;
        
        // AST_ASSIGN
        struct {
            char* var_name;
            struct ast_node* expr;
        } assign;
        
        // AST_DECL
        struct {
            char* var_name;
            // type 信息存储在符号表
        } decl;
        
        // AST_WHILE
        struct {
            struct ast_node* condition;
            struct ast_node* body;
        } while_loop;
        
        // AST_IF
        struct {
            struct ast_node* condition;
            struct ast_node* then_branch;
            struct ast_node* else_branch;
        } if_stmt;
        
        // AST_SEQ
        struct {
            struct ast_node** statements;
            size_t count;
        } seq;
        
    } data;
} ast_node_t;

/* 构造函数 */
ast_node_t* ast_number_new(long value, int line, int column);
ast_node_t* ast_ident_new(const char* name, int line, int column);
ast_node_t* ast_binop_new(binop_t op, ast_node_t* left, ast_node_t* right);
ast_node_t* ast_unop_new(unop_t op, ast_node_t* operand);
ast_node_t* ast_assign_new(const char* var_name, ast_node_t* expr);
ast_node_t* ast_decl_new(const char* var_name, int line, int column);
ast_node_t* ast_while_new(ast_node_t* condition, ast_node_t* body);
ast_node_t* ast_if_new(ast_node_t* condition, ast_node_t* then_branch, ast_node_t* else_branch);
ast_node_t* ast_seq_new(ast_node_t** statements, size_t count);
ast_node_t* ast_cast_new(ast_node_t* expr);
ast_node_t* ast_deref_new(ast_node_t* expr);
ast_node_t* ast_address_new(ast_node_t* expr);

/* 析构函数 */
void ast_node_free(ast_node_t* node);

/* 工具函数 */
void ast_print(ast_node_t* node, int indent);

#endif // AST_H
