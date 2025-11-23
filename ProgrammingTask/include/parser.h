#ifndef PARSER_H
#define PARSER_H

#include "ast.h"

/**
 * 解析函数
 */
ast_node_t* parse_program(const char* input);

/* 错误恢复 */
typedef void (*parse_error_handler_t)(int line, int column, const char* message);
void parser_set_error_handler(parse_error_handler_t handler);

#endif // PARSER_H
