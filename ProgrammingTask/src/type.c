#include "type.h"
#include <stdlib.h>
#include <stdio.h>
#include "util.h"

Type *type_make_basic(TypeKind kind) {
	Type *t = (Type *)xmalloc(sizeof(Type));
	t->kind = kind;
	t->base = NULL;
	return t;
}

Type *type_make_ptr(Type *base) {
	Type *t = (Type *)xmalloc(sizeof(Type));
	t->kind = TYPE_PTR;
	t->base = base;
	return t;
}

bool type_equal(Type *a, Type *b) {
	if (a == b) return true;
	if (!a || !b) return false;
	if (a->kind != b->kind) return false;
	if (a->kind == TYPE_PTR) return type_equal(a->base, b->base);
	return true;
}

bool type_is_integer(Type *t) {
	if (!t) return false;
	return (t->kind == TYPE_SHORT || t->kind == TYPE_INT || t->kind == TYPE_LONG || t->kind == TYPE_LLONG);
}

bool type_is_pointer(Type *t) {
	return t && t->kind == TYPE_PTR;
}

int type_rank(Type *t) {
	if (!t) return 0;
	switch (t->kind) {
		case TYPE_SHORT: return 1;
		case TYPE_INT:   return 2;
		case TYPE_LONG:  return 3;
		case TYPE_LLONG: return 4;
		default: return 0;
	}
}

bool type_can_convert(Type *from, Type *to) {
	if (!from || !to) return false;
	if (to->kind == TYPE_ERROR || from->kind == TYPE_ERROR) return true;
	if (type_equal(from, to)) return true;
	if (type_is_integer(from) && type_is_integer(to)) return true; /* allow integer promotions/conversions */
	if (type_is_pointer(from) && type_is_pointer(to)) {
		/* allow pointer conversion only when base types are equal */
		return type_equal(from->base, to->base);
	}
	return false;
}

Type *type_common(Type *a, Type *b) {
	if (!a || !b) return type_make_basic(TYPE_ERROR);
	if (a->kind == TYPE_ERROR || b->kind == TYPE_ERROR) return type_make_basic(TYPE_ERROR);
	if (type_is_integer(a) && type_is_integer(b)) {
		/* choose the higher-ranked integer type */
		int ra = type_rank(a), rb = type_rank(b);
		return type_make_basic(ra >= rb ? a->kind : b->kind);
	}
	if (type_is_pointer(a) && type_is_pointer(b)) {
		if (!a->base || !b->base) return type_make_basic(TYPE_ERROR);
		if (type_equal(a->base, b->base)) return type_make_ptr(a->base);
		return type_make_basic(TYPE_ERROR);
	}
	return type_make_basic(TYPE_ERROR);
}

void type_free(Type *t) {
	if (!t) return;
	if (t->kind == TYPE_PTR && t->base) {
		type_free(t->base);
	}
	free(t);
}

void type_print(Type *t) {
	if (!t) { printf("<null>"); return; }
	switch (t->kind) {
		case TYPE_SHORT: printf("short"); break;
		case TYPE_INT:   printf("int"); break;
		case TYPE_LONG:  printf("long"); break;
		case TYPE_LLONG: printf("long long"); break;
		case TYPE_PTR:   type_print(t->base); printf("*"); break;
		case TYPE_ERROR: printf("<error>"); break;
		default: printf("<unknown>"); break;
	}
}
