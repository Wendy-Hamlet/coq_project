/* 空的源文件占位符 - 将在实现阶段填充 */
#include <stdio.h>
#include <stdlib.h>
#include "ast.h"
#include "analyze.h"

extern int yyparse();
extern FILE *yyin;

extern Stmt *parse_result; 

int main(int argc, char **argv) {
    // 1. 处理输入文件
    if (argc > 1) {
        FILE *f = fopen(argv[1], "r");
        if (!f) {
            perror(argv[1]);
            return 1;
        }
        yyin = f;
    } else {
        // read from stdin for debug(if no arg)
        // printf("Reading from stdin...\n");
    }

    // Parsing
    if (yyparse() != 0) {
        fprintf(stderr, "Parsing failed\n");
        return 1;
    }

    // Semantic Analysis
    if (parse_result != NULL) {
        analyze(parse_result);
        printf("Semantic analysis completed successfully.\n");
        
        // 4. print (optional)
        // ast_print_stmt(parse_result, 0);
    }

    return 0;
}