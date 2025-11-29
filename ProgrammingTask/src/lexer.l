%{
/* Lexer for typed WhileD language */
#include "ast.h"
#include "type.h"
#include "parser.h"
#include <string.h>
#include "util.h"

/* Update line number on newlines */
%}

%option noyywrap
%option yylineno

%%

[ \t\r]+              { /* skip whitespace */ }
\n                    { /* skip newlines */ }
#.*                   { /* skip comments */ }

"skip"                { return SKIP; }
"if"                  { return IF; }
"then"                { return THEN; }
"else"                { return ELSE; }
"fi"                  { return FI; }
"while"               { return WHILE; }
"do"                  { return DO; }
"od"                  { return OD; }

"short"               { return SHORT; }
"int"                 { return INT; }
"long"                { return LONG; }
"long"[ \t\r\n]+"long"  { return LONGLONG; }

":="                  { return ASSIGN; }
";"                   { return SEMI; }
"("                   { return LPAREN; }
")"                   { return RPAREN; }

"+"                   { return PLUS; }
"-"                   { return MINUS; }
"*"                   { return STAR; }
"/"                   { return SLASH; }
"%"                   { return MOD; }

"=="                  { return EQ; }
"!="                  { return NEQ; }
"<"                   { return LT; }
">"                   { return GT; }
"<="                  { return LE; }
">="                  { return GE; }

"&"                   { return AMPERSAND; }

[0-9]+                { 
                        yylval.int_val = atoll(yytext); 
                        return INT_LITERAL; 
                      }

[a-zA-Z_][a-zA-Z0-9_]* { 
                        yylval.str_val = xstrdup(yytext); 
                        return IDENT; 
                      }

.                     { 
                        fprintf(stderr, "Lexical error: unexpected character '%c' at line %d\n", 
                                yytext[0], yylineno);
                        exit(1);
                      }

%%
