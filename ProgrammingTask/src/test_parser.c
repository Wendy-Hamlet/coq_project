#include <stdio.h>
#include <stdlib.h>
#include "type.h"    // 确保 Type 结构优先定义
#include "ast.h"     // 确保 Expr 和 Stmt 结构优先定义
#include "parser.h"  // 包含 Bison 生成的 token 和 YYSTYPE 定义

/* parse_result 是由 parser.y 里声明的 */
extern Stmt *parse_result;

extern int yyparse(void);
extern void yyrestart(FILE *);

int main(int argc, char **argv) {
    FILE *fp = stdin;

    if (argc == 2) {
        fp = fopen(argv[1], "r");
        if (!fp) {
            perror("Cannot open input file");
            return 1;
        }
    }

    /* 告诉 lexer 从 fp 开始读 */
    yyrestart(fp);

    printf("=== Running parser ===\n");

    int ret = yyparse();
    if (ret == 0) {
        printf(">>> Parse SUCCESS!\n");
    } else {
        printf(">>> Parse FAILED!\n");
        return 1;
    }

    if (parse_result == NULL) {
        printf(">>> Parser returned NULL AST (maybe SKIP or empty input)\n");
        return 0;
    }

    printf("\n=== AST Result ===\n");

    /* 如果你有 ast_printer，可以打印 AST */
#ifdef AST_PRINTER_AVAILABLE
    extern void ast_print(Stmt *s);
    ast_print(parse_result);
#else
    /* 没有 ast_printer 时的安全占位输出 */
    printf("[AST constructed successfully, but no printer available]\n");
#endif

    return 0;
}
