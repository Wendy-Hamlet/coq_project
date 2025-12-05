/* Driver module for the typed WhileD compiler */
#include "driver.h"
#include "analyze.h"
#include "ast.h"
#include <stdio.h>
#include <stdlib.h>

/* External references to lexer/parser globals */
extern int yyparse();
extern FILE *yyin;
extern Stmt *parse_result; /* Defined by parser.y */

int driver_compile(FILE *input) {
    if (!input) {
        fprintf(stderr, "Driver Error: Invalid input file\n");
        return 1;
    }

    /* Step 1: Set the lexer input source */
    yyin = input;

    /* Step 2: Parsing - yyparse calls yylex, builds AST into parse_result */
    if (yyparse() != 0) {
        fprintf(stderr, "Compilation Failed: Parse error\n");
        return 1;
    }

    /* Step 3: Semantic Analysis (type checking, scope management) */
    if (parse_result) {
        /* analyze() will exit(1) on error; if it returns, analysis succeeded */
        analyze(parse_result);
    }
    /* Empty input is considered valid (parse_result may be NULL) */

    /* Step 4: (Future extension) Code Generation */
    /* codegen(parse_result); */

    return 0;
}