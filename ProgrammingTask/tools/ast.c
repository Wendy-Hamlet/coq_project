#include <stdio.h>
#include <stdlib.h>
#include "ast.h"

extern int yyparse();
extern FILE *yyin;
extern Stmt *parse_result; 

int main(int argc, char **argv) {
    if (argc > 1) {
        FILE *f = fopen(argv[1], "r");
        if (!f) {
            perror(argv[1]);
            return 1;
        }
        yyin = f;
    }

    // Parse the input
    if (yyparse() != 0) {
        fprintf(stderr, "Parsing failed\n");
        return 1;
    }

    // Dump AST in function call form
    if (parse_result) {
        ast_dump_stmt(parse_result, 0); 
    }

    return 0;
}
