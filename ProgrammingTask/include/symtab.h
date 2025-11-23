#ifndef SYMTAB_H
#define SYMTAB_H

#include "type.h"

/**
 * 符号表项
 */
typedef struct symbol {
    char* name;
    type_t* type;
    int is_initialized;
    int line_declared;    // 声明行号
} symbol_t;

/**
 * 作用域
 */
typedef struct scope {
    symbol_t** symbols;
    int count;
    int capacity;
    struct scope* parent;  // 指向外层作用域
} scope_t;

/* 符号表接口 */
void symtab_init(void);
void symtab_cleanup(void);

/* 作用域操作 */
void symtab_push_scope(void);
void symtab_pop_scope(void);

/* 符号操作 */
int symtab_insert(const char* name, type_t* type, int line);
symbol_t* symtab_lookup(const char* name);
int symtab_is_declared(const char* name);
void symtab_mark_initialized(const char* name);

/* 错误处理 */
typedef void (*error_handler_t)(const char* message);
void symtab_set_error_handler(error_handler_t handler);

#endif // SYMTAB_H
