#include "ast.h"
#include "type.h"
#include "../build/parser.h"
#include <stdio.h>
#include <stdlib.h>

extern int yylex();
extern char *yytext;
extern int yylineno;
extern FILE *yyin;

/* Define yylval here since we are not linking parser.c */
YYSTYPE yylval;

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
