#include "symtab.h"
#include "util.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Create a new scope */
SymTab *symtab_push(SymTab *parent) {
  SymTab *tab = (SymTab *)xmalloc(sizeof(SymTab));
  tab->symbols = NULL;
  tab->parent = parent;
  return tab;
}

/* Exit current scope */
SymTab *symtab_pop(SymTab *tab) {
  if (!tab)
    return NULL;

  SymTab *parent = tab->parent;
  Symbol *s = tab->symbols;
  while (s) {
    Symbol *next = s->next;
    /* We own the name string copy */
    if (s->name)
      free((void *)s->name);
    /* We do NOT own the Type* (it might be shared), so we don't free it here.
     * In a more complex compiler, types would be managed by a pool or
     * refcounted. */
    free(s);
    s = next;
  }
  free(tab);
  return parent;
}

/* Insert a symbol into the CURRENT scope */
bool symtab_insert(SymTab *tab, const char *name, Type *type) {
  if (!tab || !name)
    return false;

  /* Check for duplicate in current scope only */
  Symbol *s = tab->symbols;
  while (s) {
    if (strcmp(s->name, name) == 0) {
      return false; /* Already exists in this scope */
    }
    s = s->next;
  }

  /* Insert new symbol at head */
  Symbol *new_sym = (Symbol *)xmalloc(sizeof(Symbol));
  new_sym->name = xstrdup(name);
  new_sym->type = type;
  new_sym->next = tab->symbols;
  tab->symbols = new_sym;

  return true;
}

/* Lookup a symbol in current or parent scopes */
Symbol *symtab_lookup(SymTab *tab, const char *name) {
  if (!name)
    return NULL;

  SymTab *current = tab;
  while (current) {
    Symbol *s = current->symbols;
    while (s) {
      if (strcmp(s->name, name) == 0) {
        return s;
      }
      s = s->next;
    }
    current = current->parent;
  }
  return NULL;
}

/* Debug print */
void symtab_print(SymTab *tab) {
  SymTab *current = tab;
  int level = 0;
  while (current) {
    printf("Scope %d:\n", level);
    Symbol *s = current->symbols;
    while (s) {
      printf("  %s: ", s->name);
      type_print(s->type);
      printf("\n");
      s = s->next;
    }
    current = current->parent;
    level++;
  }
}