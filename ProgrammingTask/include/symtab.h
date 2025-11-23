#ifndef SYMTAB_H
#define SYMTAB_H

#include "type.h"
#include <stdbool.h>

typedef struct Symbol {
    const char *name;
    Type *type;
    struct Symbol *next;
} Symbol;

typedef struct SymTab {
    Symbol *symbols;
    struct SymTab *parent;
} SymTab;

/* Scope management */
SymTab *symtab_push(SymTab *parent);
SymTab *symtab_pop(SymTab *tab);

/* Insert and lookup */
bool symtab_insert(SymTab *tab, const char *name, Type *type);
Symbol *symtab_lookup(SymTab *tab, const char *name);

/* Debug */
void symtab_print(SymTab *tab);

#endif
