#ifndef LEXER_H
#define LEXER_H

/**
 * Token 类型
 */
typedef enum {
    // 关键字
    TOKEN_SHORT,
    TOKEN_INT,
    TOKEN_LONG,
    TOKEN_WHILE,
    TOKEN_DO,
    TOKEN_OD,
    TOKEN_IF,
    TOKEN_THEN,
    TOKEN_ELSE,
    TOKEN_FI,
    TOKEN_SKIP,

    // 标识符和字面量
    TOKEN_IDENT,
    TOKEN_NUMBER,

    // 运算符
    TOKEN_ASSIGN,        // :=
    TOKEN_PLUS,          // +
    TOKEN_MINUS,         // -
    TOKEN_MULT,          // *
    TOKEN_DIV,           // /
    TOKEN_MOD,           // %
    TOKEN_EQ,            // =
    TOKEN_NE,            // !=
    TOKEN_LT,            // <
    TOKEN_LE,            // <=
    TOKEN_GT,            // >
    TOKEN_GE,            // >=
    TOKEN_AND,           // &&
    TOKEN_OR,            // ||
    TOKEN_NOT,           // !
    TOKEN_AMPERSAND,     // &
    TOKEN_SEMICOLON,     // ;
    TOKEN_LPAREN,        // (
    TOKEN_RPAREN,        // )
    TOKEN_COMMA,         // ,

    // 特殊
    TOKEN_EOF,
    TOKEN_ERROR

} token_type_t;

/**
 * Token 结构
 */
typedef struct {
    token_type_t type;
    char* value;         // 对于 TOKEN_IDENT 和 TOKEN_NUMBER
    int line;
    int column;
} token_t;

/* 词法分析接口 */
token_t* lex_next_token(void);
void lex_reset(const char* input);
void lex_cleanup(void);

/* 工具函数 */
const char* token_type_to_string(token_type_t type);

#endif // LEXER_H
