#ifndef DRIVER_H
#define DRIVER_H

#include <stdio.h>

/**
 * 编译驱动入口
 * @param input 打开的文件指针 (如果是 stdin 则传入 stdin)
 * @return 0 表示成功，非 0 表示失败
 */
int driver_compile(FILE *input);

#endif