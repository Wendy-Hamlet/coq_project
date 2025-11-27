/* bison会自动生成parser.h文件，所以这里不再需要这个文件 */
#ifndef PARSER_H
#define PARSER_H

#include "ast.h"

/* Bison-generated parser function */
int yyparse(void);

/* Error reporting */
void yyerror(const char *s);

/* Global parse result - set by parser */
extern Stmt *parse_result;

#endif
