/* 空的源文件占位符 - 将在实现阶段填充 */
#include "driver.h"
#include "analyze.h"
#include "ast.h"
#include <stdio.h>
#include <stdlib.h>

/* 引用外部定义的全局变量 */
extern int yyparse();
extern FILE *yyin;
extern Stmt *parse_result; /* 由 parser.y 定义 */

int driver_compile(FILE *input) {
    if (!input) {
        fprintf(stderr, "Driver Error: Invalid input file\n");
        return 1;
    }

    /* 1. 设置词法分析器的输入源 */
    yyin = input;

    /* 2. 语法分析 (Parsing) */
    // yyparse 会自动调用 yylex，构建 AST 并赋值给 parse_result
    if (yyparse() != 0) {
        fprintf(stderr, "Compilation Failed: Parse error\n");
        return 1;
    }

    /* 3. 语义分析 (Semantic Analysis) */
    if (parse_result) {
        // analyze 函数在出错时通常直接 exit(1)，如果没退出说明成功
        analyze(parse_result);
        
        // 可以在这里添加 verbose 模式判断
        // printf("Semantic analysis completed successfully.\n");
    } else {
        // 如果是空文件，parse_result 可能为 NULL，视为合法或警告均可
    }

    /* 4. (未来扩展) 代码生成 (Code Generation) */
    // codegen(parse_result);

    return 0;
}