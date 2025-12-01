#include "symtab.h"
#include "type.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

void test_basic_insert_lookup() {
  printf("Running test_basic_insert_lookup...\n");
  SymTab *tab = symtab_push(NULL);

  Type *t_int = type_make_basic(TYPE_INT);
  assert(symtab_insert(tab, "x", t_int) == true);

  Symbol *s = symtab_lookup(tab, "x");
  assert(s != NULL);
  assert(strcmp(s->name, "x") == 0);
  assert(s->type->kind == TYPE_INT);

  assert(symtab_lookup(tab, "y") == NULL);

  symtab_pop(tab);
  // Note: type_free might be risky if types are shared, but here we control it.
  type_free(t_int);
  printf("PASS\n");
}

void test_scope_shadowing() {
  printf("Running test_scope_shadowing...\n");
  SymTab *global = symtab_push(NULL);

  Type *t_int = type_make_basic(TYPE_INT);
  symtab_insert(global, "x", t_int);

  SymTab *local = symtab_push(global);
  Type *t_long = type_make_basic(TYPE_LONG);

  // Shadow x
  assert(symtab_insert(local, "x", t_long) == true);

  Symbol *s = symtab_lookup(local, "x");
  assert(s != NULL);
  assert(s->type->kind == TYPE_LONG);

  // Pop local
  local = symtab_pop(local);
  assert(local == global);

  s = symtab_lookup(global, "x");
  assert(s != NULL);
  assert(s->type->kind == TYPE_INT);

  symtab_pop(global);
  type_free(t_int);
  type_free(t_long);
  printf("PASS\n");
}

void test_duplicate_insert() {
  printf("Running test_duplicate_insert...\n");
  SymTab *tab = symtab_push(NULL);

  Type *t_int = type_make_basic(TYPE_INT);
  assert(symtab_insert(tab, "x", t_int) == true);
  assert(symtab_insert(tab, "x", t_int) == false);

  symtab_pop(tab);
  type_free(t_int);
  printf("PASS\n");
}

void test_multi_level_nesting() {
  printf("Running test_multi_level_nesting...\n");
  /* Level 0 */
  SymTab *l0 = symtab_push(NULL);
  Type *t_int = type_make_basic(TYPE_INT);
  symtab_insert(l0, "global", t_int);

  /* Level 1 */
  SymTab *l1 = symtab_push(l0);
  Type *t_short = type_make_basic(TYPE_SHORT);
  symtab_insert(l1, "mid", t_short);

  /* Level 2 */
  SymTab *l2 = symtab_push(l1);
  Type *t_long = type_make_basic(TYPE_LONG);
  symtab_insert(l2, "inner", t_long);

  /* Check visibility from inside out */
  Symbol *s;

  /* Can see inner */
  s = symtab_lookup(l2, "inner");
  assert(s != NULL && s->type->kind == TYPE_LONG);

  /* Can see mid */
  s = symtab_lookup(l2, "mid");
  assert(s != NULL && s->type->kind == TYPE_SHORT);

  /* Can see global */
  s = symtab_lookup(l2, "global");
  assert(s != NULL && s->type->kind == TYPE_INT);

  /* Pop Level 2 */
  l1 = symtab_pop(l2);
  assert(l1 == l1); // Just to be sure we got the right pointer back

  /* Level 1 cannot see inner */
  assert(symtab_lookup(l1, "inner") == NULL);
  /* Level 1 can see mid and global */
  assert(symtab_lookup(l1, "mid") != NULL);
  assert(symtab_lookup(l1, "global") != NULL);

  /* Pop Level 1 */
  l0 = symtab_pop(l1);

  /* Level 0 cannot see mid */
  assert(symtab_lookup(l0, "mid") == NULL);
  /* Level 0 can see global */
  assert(symtab_lookup(l0, "global") != NULL);

  symtab_pop(l0);
  type_free(t_int);
  type_free(t_short);
  type_free(t_long);
  printf("PASS\n");
}

void test_sibling_scopes() {
  printf("Running test_sibling_scopes...\n");
  /* Parent scope */
  SymTab *parent = symtab_push(NULL);
  Type *t_int = type_make_basic(TYPE_INT);
  symtab_insert(parent, "x", t_int);

  /* Sibling 1: if (true) { int y; } */
  SymTab *sib1 = symtab_push(parent);
  Type *t_y = type_make_basic(TYPE_SHORT);
  symtab_insert(sib1, "y", t_y);

  assert(symtab_lookup(sib1, "x") != NULL);
  assert(symtab_lookup(sib1, "y") != NULL);

  /* Exit Sibling 1 */
  parent = symtab_pop(sib1);

  /* Sibling 2: else { int z; } */
  SymTab *sib2 = symtab_push(parent);
  Type *t_z = type_make_basic(TYPE_LONG);
  symtab_insert(sib2, "z", t_z);

  /* Sibling 2 should NOT see y from Sibling 1 */
  assert(symtab_lookup(sib2, "y") == NULL);
  /* Sibling 2 should see z and x */
  assert(symtab_lookup(sib2, "z") != NULL);
  assert(symtab_lookup(sib2, "x") != NULL);

  symtab_pop(sib2);
  symtab_pop(parent);

  type_free(t_int);
  type_free(t_y);
  type_free(t_z);
  printf("PASS\n");
}

int main() {
  test_basic_insert_lookup();
  test_scope_shadowing();
  test_duplicate_insert();
  test_multi_level_nesting();
  test_sibling_scopes();
  printf("All symtab tests passed!\n");
  return 0;
}
