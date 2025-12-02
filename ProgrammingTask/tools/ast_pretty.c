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
    } else {
        // fprintf(stderr, "Usage: %s <input_file>\n", argv[0]);
        // return 1;
    }

    // 2. Parse 
    if (yyparse() != 0) {
        fprintf(stderr, "Parsing failed\n");
        return 1;
    }

    // 3. print AST 
    if (parse_result) {
        ast_print_stmt(parse_result, 0); 
    }

    return 0;
}