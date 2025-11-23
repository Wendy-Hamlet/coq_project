#ifndef TYPE_H
#define TYPE_H

/**
 * 基本类型枚举
 */
typedef enum {
    TYPE_SHORT,       // short
    TYPE_INT,         // int
    TYPE_LONG,        // long
    TYPE_LONG_LONG,   // long long
    TYPE_VOID,        // void (暂未使用)
    TYPE_ERROR        // 错误类型
} base_type_t;

/**
 * 完整类型表示（支持指针）
 */
typedef struct type {
    base_type_t base;
    int pointer_level;  // 0: 非指针，1: T*，2: T**，等等
} type_t;

/* 类型构造函数 */
type_t* type_new(base_type_t base, int pointer_level);
type_t* type_copy(const type_t* type);
void type_free(type_t* type);

/* 类型比较 */
int type_equal(const type_t* t1, const type_t* t2);
int type_compatible(const type_t* from, const type_t* to);

/* 类型转换规则 */
type_t* type_promote(const type_t* t1, const type_t* t2);
int type_can_cast(const type_t* from, const type_t* to);

/* 判断函数 */
int type_is_integer(const type_t* type);
int type_is_pointer(const type_t* type);
int type_is_numeric(const type_t* type);

/* 字符串表示 */
char* type_to_string(const type_t* type);
const char* base_type_to_string(base_type_t base);

#endif // TYPE_H
