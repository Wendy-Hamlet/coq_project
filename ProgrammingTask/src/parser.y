%{
/* Parser for typed WhileD language */
#include "ast.h"
#include "type.h"
#include <stdio.h>
#include <stdlib.h>

/* Interface to lexer */
extern int yylex();
extern int yylineno;
void yyerror(const char *s);

/* Global parse result */
Stmt *parse_result = NULL;
%}

%union {
    long long int_val;
    char *str_val;
    Type *type_val;
    Expr *expr_val;
    Stmt *stmt_val;
}

/* Terminal tokens */
%token SKIP IF THEN ELSE FI WHILE DO OD
%token SHORT INT LONG LONGLONG
%token ASSIGN SEMI LPAREN RPAREN
%token PLUS MINUS STAR SLASH MOD
%token EQ NEQ LT GT LE GE
%token AMPERSAND
%token <int_val> INT_LITERAL
%token <str_val> IDENT

/* Non-terminals with types */
%type <type_val> type basetype
%type <expr_val> expr term factor
%type <stmt_val> program commands command

/* Operator precedence and associativity */
%left EQ NEQ
%left LT GT LE GE
%left PLUS MINUS
%left STAR SLASH MOD
%right CAST      /* for type casting (Type) expr */
%right UNARY     /* for unary minus and address/deref */

%%

/* Program is a sequence of commands */
program:
    commands                { parse_result = $1; }
    ;

commands:
    command                 { $$ = $1; }
    | commands SEMI command { $$ = ast_seq($1, $3); }
    ;

command:
    SKIP                    { $$ = ast_skip(); }
    | IDENT ASSIGN expr     { $$ = ast_assign($1, $3); }
    | type IDENT SEMI command
                            { $$ = ast_decl($1, $2, $4); }
    | IF expr THEN commands ELSE commands FI
                            { $$ = ast_if($2, $4, $6); }
    | WHILE expr DO commands OD
                            { $$ = ast_while($2, $4); }
    ;

/* Type grammar */
type:
    basetype                { $$ = $1; }
    | type STAR             { $$ = type_make_ptr($1); }
    ;

/* LONG LONG changed to LONGLONG */
basetype:
    SHORT                   { $$ = type_make_basic(TYPE_SHORT); }
    | INT                   { $$ = type_make_basic(TYPE_INT); }
    | LONG                  { $$ = type_make_basic(TYPE_LONG); }
    | LONGLONG              { $$ = type_make_basic(TYPE_LLONG); }
    ;

/* Expression grammar */
expr:
    term                    { $$ = $1; }
    | expr PLUS term        { $$ = ast_binop(BIN_ADD, $1, $3); }
    | expr MINUS term       { $$ = ast_binop(BIN_SUB, $1, $3); }
    | expr EQ term          { $$ = ast_binop(BIN_EQ, $1, $3); }
    | expr NEQ term         { $$ = ast_binop(BIN_NEQ, $1, $3); }
    | expr LT term          { $$ = ast_binop(BIN_LT, $1, $3); }
    | expr GT term          { $$ = ast_binop(BIN_GT, $1, $3); }
    | expr LE term          { $$ = ast_binop(BIN_LE, $1, $3); }
    | expr GE term          { $$ = ast_binop(BIN_GE, $1, $3); }
    ;

term:
    factor                  { $$ = $1; }
    | term STAR factor      { $$ = ast_binop(BIN_MUL, $1, $3); }
    | term SLASH factor     { $$ = ast_binop(BIN_DIV, $1, $3); }
    | term MOD factor       { $$ = ast_binop(BIN_MOD, $1, $3); }
    ;

factor:
    INT_LITERAL             { $$ = ast_int_literal($1); }
    | IDENT                 { $$ = ast_var($1); }
    | LPAREN expr RPAREN    { $$ = $2; }
    | LPAREN type RPAREN factor %prec CAST
                            { $$ = ast_cast($2, $4); }
    | MINUS factor %prec UNARY
                            { $$ = ast_unop($2); }
    | STAR factor %prec UNARY
                            { $$ = ast_deref($2); }
    | AMPERSAND IDENT %prec UNARY
                            { $$ = ast_addr(ast_var($2)); }
    ;

%%

void yyerror(const char *s) {
    fprintf(stderr, "Parse error at line %d: %s\n", yylineno, s);
}
