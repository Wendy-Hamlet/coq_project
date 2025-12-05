#include <stdio.h>
#include <stdlib.h>
#include "driver.h" 

int main(int argc, char **argv) {
    FILE *input = stdin;

    // 1. 处理命令行参数
    if (argc > 1) {
        input = fopen(argv[1], "r");
        if (!input) {
            perror(argv[1]);
            return 1;
        }
    }

    // 2. 将控制权交给 Driver
    int result = driver_compile(input);

    // 3. 清理资源
    if (input != stdin) {
        fclose(input);
    }

    return result;
}