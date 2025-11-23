#ifndef UTIL_H
#define UTIL_H

#include <stddef.h>

/* 内存管理 */
void* xmalloc(size_t size);
void* xcalloc(size_t count, size_t size);
void* xrealloc(void* ptr, size_t size);
void xfree(void* ptr);

/* 字符串操作 */
char* xstrdup(const char* str);
char* xstrndup(const char* str, size_t len);

/* 错误处理 */
void error(const char* fmt, ...);
void warning(const char* fmt, ...);
void info(const char* fmt, ...);

/* 文件操作 */
char* read_file(const char* filename);

#endif // UTIL_H
