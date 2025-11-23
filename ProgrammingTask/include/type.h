#ifndef TYPE_H
#define TYPE_H

#include <stdbool.h>
#include <stddef.h>

typedef enum {
    TYPE_SHORT,
    TYPE_INT,
    TYPE_LONG,
    TYPE_LLONG,
    TYPE_PTR,       // pointer to another type
    TYPE_ERROR      // used for type-checking failure recovery
} TypeKind;

typedef struct Type {
    TypeKind kind;
    struct Type *base;     // NULL unless kind == TYPE_PTR
} Type;

/* Constructors */
Type *type_make_basic(TypeKind k);
Type *type_make_ptr(Type *base);

/* Type comparison */
bool type_equal(Type *a, Type *b);

/* Type utilities */
bool type_is_integer(Type *t);
bool type_is_pointer(Type *t);
int  type_rank(Type *t);       // for implicit conversion ranking

/* Type conversion check */
bool type_can_convert(Type *from, Type *to);
Type *type_common(Type *a, Type *b);  // find common type for binary op

/* Memory deallocation */
void type_free(Type *t);

/* Pretty printing */
void type_print(Type *t);

#endif
