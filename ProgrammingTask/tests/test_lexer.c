#include "ast.h"
#include "type.h"
#include "parser.h"
#include <stdio.h>
#include <stdlib.h>

extern int yylex();
extern char *yytext;
extern int yylineno;
extern FILE *yyin;

/* Minimal stubs to satisfy linker when parser.o calls AST/type helpers. */
Expr *ast_int_literal(long long v) { (void)v; return NULL; }
Expr *ast_var(const char *name) { (void)name; return NULL; }
Expr *ast_binop(BinOp op, Expr *l, Expr *r) { (void)op; (void)l; (void)r; return NULL; }
Expr *ast_unop(Expr *e) { (void)e; return NULL; }
Expr *ast_addr(Expr *e) { (void)e; return NULL; }
Expr *ast_deref(Expr *e) { (void)e; return NULL; }
Expr *ast_cast(Type *t, Expr *e) { (void)t; (void)e; return NULL; }

Stmt *ast_skip() { return NULL; }
Stmt *ast_seq(Stmt *s1, Stmt *s2) { (void)s1; (void)s2; return NULL; }
Stmt *ast_assign(const char *lhs, Expr *rhs) { (void)lhs; (void)rhs; return NULL; }
Stmt *ast_decl(Type *t, const char *var, Stmt *body) { (void)t; (void)var; (void)body; return NULL; }
Stmt *ast_if(Expr *c, Stmt *t, Stmt *e) { (void)c; (void)t; (void)e; return NULL; }
Stmt *ast_while(Expr *c, Stmt *body) { (void)c; (void)body; return NULL; }

Type *type_make_basic(TypeKind k) { (void)k; return NULL; }
Type *type_make_ptr(Type *base) { (void)base; return NULL; }

const char *token_name(int token) {
  switch (token) {
  case SKIP: return "SKIP";
  case IF: return "IF";
  case THEN: return "THEN";
  case ELSE: return "ELSE";
  case FI: return "FI";
  case WHILE: return "WHILE";
  case DO: return "DO";
  case OD: return "OD";
  case SHORT: return "SHORT";
  case INT: return "INT";
  case LONG: return "LONG";
  case ASSIGN: return "ASSIGN";
  case SEMI: return "SEMI";
  case LPAREN: return "LPAREN";
  case RPAREN: return "RPAREN";
  case PLUS: return "PLUS";
  case MINUS: return "MINUS";
  case STAR: return "STAR";
  case SLASH: return "SLASH";
  case MOD: return "MOD";
  case EQ: return "EQ";
  case NEQ: return "NEQ";
  case LT: return "LT";
  case GT: return "GT";
  case LE: return "LE";
  case GE: return "GE";
  case AMPERSAND: return "AMPERSAND";
  case INT_LITERAL: return "INT_LITERAL";
  case IDENT: return "IDENT";
  default: return "UNKNOWN";
  }
}

int main(int argc, char **argv) {
  if (argc > 1) {
    yyin = fopen(argv[1], "r");
    if (!yyin) {
      perror(argv[1]);
      return 1;
    }
  }

  int token;
  while ((token = yylex())) {
    printf("Line %d: Token %s (%s)\n", yylineno, token_name(token), yytext);
  }
  return 0;
}
