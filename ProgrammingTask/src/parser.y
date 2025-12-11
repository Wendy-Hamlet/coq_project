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
%token ASSIGN SEMI LPAREN RPAREN LBRACE RBRACE
%token PLUS MINUS STAR SLASH MOD
%token EQ NEQ LT GT LE GE
%token AND OR NOT AMPERSAND
%token <int_val> INT_LITERAL
%token <str_val> IDENT

/* Non-terminals with types */
%type <type_val> type basetype
%type <expr_val> expr logic_or logic_and comparison additive term factor unary
%type <stmt_val> program commands command

/* Operator precedence and associativity */
%left OR
%left AND
%left EQ NEQ
%left LT GT LE GE
%left PLUS MINUS
%left STAR SLASH MOD
%right CAST
%right UNARY

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
    | STAR unary ASSIGN expr
                            { $$ = ast_assign_deref($2, $4); }
    | type IDENT SEMI command
                            { $$ = ast_decl($1, $2, $4); }
    | IF LPAREN expr RPAREN THEN LBRACE commands RBRACE ELSE LBRACE commands RBRACE
                            { $$ = ast_if($3, $7, $11); }
    | WHILE LPAREN expr RPAREN DO LBRACE commands RBRACE
                            { $$ = ast_while($3, $7); }
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

/* Expression grammar with proper precedence */
expr:
    logic_or                { $$ = $1; }
    ;

logic_or:
    logic_and               { $$ = $1; }
    | logic_or OR logic_and { $$ = ast_binop(BIN_OR, $1, $3); }
    ;

logic_and:
    comparison              { $$ = $1; }
    | logic_and AND comparison
                            { $$ = ast_binop(BIN_AND, $1, $3); }
    ;

comparison:
    additive                { $$ = $1; }
    | comparison EQ additive  { $$ = ast_binop(BIN_EQ, $1, $3); }
    | comparison NEQ additive { $$ = ast_binop(BIN_NEQ, $1, $3); }
    | comparison LT additive  { $$ = ast_binop(BIN_LT, $1, $3); }
    | comparison GT additive  { $$ = ast_binop(BIN_GT, $1, $3); }
    | comparison LE additive  { $$ = ast_binop(BIN_LE, $1, $3); }
    | comparison GE additive  { $$ = ast_binop(BIN_GE, $1, $3); }
    ;

additive:
    term                    { $$ = $1; }
    | additive PLUS term    { $$ = ast_binop(BIN_ADD, $1, $3); }
    | additive MINUS term   { $$ = ast_binop(BIN_SUB, $1, $3); }
    ;

term:
    unary                   { $$ = $1; }
    | term STAR unary       { $$ = ast_binop(BIN_MUL, $1, $3); }
    | term SLASH unary      { $$ = ast_binop(BIN_DIV, $1, $3); }
    | term MOD unary        { $$ = ast_binop(BIN_MOD, $1, $3); }
    ;

unary:
    factor                  { $$ = $1; }
    | MINUS unary %prec UNARY
                            { $$ = ast_unop($2); }
    | NOT unary %prec UNARY
                            { $$ = ast_not($2); }
    | STAR unary %prec UNARY
                            { $$ = ast_deref($2); }
    | AMPERSAND unary %prec UNARY
                            { $$ = ast_addr($2); }   /* Allows &x, &(*ptr), etc. */
    ;

factor:
    INT_LITERAL             { $$ = ast_int_literal($1); }
    | IDENT                 { $$ = ast_var($1); }
    | LPAREN expr RPAREN    { $$ = $2; }
    | LPAREN type RPAREN unary %prec CAST
                            { $$ = ast_cast($2, $4); }
    ;

%%

void yyerror(const char *s) {
    fprintf(stderr, "Parse error at line %d: %s\n", yylineno, s);
}
