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
