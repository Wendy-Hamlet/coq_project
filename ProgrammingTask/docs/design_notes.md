# 设计说明

本文档说明带类型 WhileD 编译器的设计决策和实现细节。

## 1. 整体架构

### 1.1 编译流程

```
源代码 (.wd)
    ↓
词法分析 (Flex)
    ↓
语法分析 (Bison) + 语义动作
    ↓
抽象语法树 (AST)
    ↓
语义分析 (类型检查)
    ↓
带类型的 AST
```

### 1.2 模块划分

| 模块 | 文件 | 功能 |
|------|------|------|
| 词法分析 | `lexer.l` | Token 识别 |
| 语法分析 | `parser.y` | 语法规则、AST 构建 |
| AST | `ast.c/h` | 语法树节点定义与构造 |
| 类型系统 | `type.c/h` | 类型表示与操作 |
| 符号表 | `symtab.c/h` | 变量管理、作用域 |
| 语义分析 | `analyze.c/h` | 类型检查、错误检测 |
| 驱动 | `driver.c/h` | 编译流程控制 |
| 主程序 | `main.c` | 入口点 |

---

## 2. 抽象语法树设计

### 2.1 表达式节点

```c
typedef enum {
    AST_INT_LITERAL,   // 整数常量
    AST_VAR,           // 变量引用
    AST_BINOP,         // 二元运算（包括 +,-,*,/,%,==,!=,<,>,<=,>=,&&,||）
    AST_UNOP,          // 一元负号
    AST_NOT,           // 逻辑非 (!)
    AST_CAST,          // 类型转换
    AST_ADDR,          // 取地址 (&)
    AST_DEREF          // 解引用 (*)
} ExprKind;

typedef struct Expr {
    ExprKind kind;
    Type *expr_type;   // 类型推断结果
    Type *cast_to;     // 隐式转换目标类型（可为 NULL）
    union { ... } v;   // 节点数据
} Expr;
```

### 2.2 语句节点

```c
typedef enum {
    STMT_SKIP,         // 空语句
    STMT_SEQ,          // 语句序列
    STMT_ASSIGN,       // 赋值
    STMT_ASSIGN_DEREF, // 解引用赋值 (*e1 = e2)
    STMT_DECL,         // 变量声明
    STMT_IF,           // 条件语句
    STMT_WHILE         // 循环语句
} StmtKind;

typedef struct Stmt {
    StmtKind kind;
    union { ... } v;   // 节点数据
} Stmt;
```

### 2.3 设计特点

1. **统一表示**：含隐式类型转换和不含隐式类型转换的 AST 使用相同的结构
2. **类型标注**：每个表达式节点有 `expr_type` 字段存储推断类型
3. **惰性转换**：隐式转换通过 `cast_to` 标记，不创建新节点

---

## 3. 类型系统设计

### 3.1 类型表示

```c
typedef enum {
    TYPE_SHORT,
    TYPE_INT,
    TYPE_LONG,
    TYPE_LLONG,
    TYPE_PTR,          // 指针类型
    TYPE_ERROR         // 错误类型（用于错误恢复）
} TypeKind;

typedef struct Type {
    TypeKind kind;
    struct Type *base; // 指针的基类型
} Type;
```

### 3.2 类型比较

- `type_equal()`: 严格类型相等
- `type_is_integer()`: 判断是否为整数类型
- `type_is_pointer()`: 判断是否为指针类型
- `type_rank()`: 获取类型等级（用于隐式转换）

### 3.3 类型转换

- `type_can_convert()`: 判断是否可以转换
- `type_common()`: 计算二元运算的结果类型

---

## 4. 符号表设计

### 4.1 数据结构

```c
typedef struct Symbol {
    const char *name;  // 变量名
    Type *type;        // 变量类型
    struct Symbol *next;
} Symbol;

typedef struct SymTab {
    Symbol *symbols;   // 当前作用域的符号链表
    struct SymTab *parent; // 父作用域
} SymTab;
```

### 4.2 作用域管理

- `symtab_push()`: 进入新作用域
- `symtab_pop()`: 退出当前作用域
- `symtab_insert()`: 在当前作用域插入符号
- `symtab_lookup()`: 从当前作用域向上查找符号

### 4.3 作用域策略

- **声明不创建作用域**：变量声明插入当前作用域
- **if/while 创建作用域**：分支和循环体有独立作用域
- **向上查找**：变量查找从当前作用域逐层向上

---

## 5. 语义分析

### 5.1 分析流程

1. 创建全局作用域
2. 递归遍历 AST
3. 对每个节点进行类型检查
4. 在表达式节点标注推断类型
5. 检测并报告语义错误

### 5.2 类型推断规则

| 表达式类型 | 推断规则 |
|-----------|----------|
| 整数常量 | `long long`（最大容量） |
| 变量引用 | 查符号表获取类型 |
| 二元运算 (+,-,*,/,%) | `type_common(左, 右)` |
| 比较运算 (==,!=,<,>,<=,>=) | `int` |
| 逻辑运算 (&&, \|\|) | `int` |
| 逻辑非 (!) | `int` |
| 一元负号 | 与操作数类型相同 |
| 取地址 | `pointer(操作数类型)` |
| 解引用 | `base(操作数类型)` |
| 类型转换 | 目标类型 |

### 5.3 错误处理

遇到语义错误时：
1. 打印详细错误信息（包含变量名或操作）
2. 调用 `exit(1)` 终止编译

---

## 6. 词法分析实现

### 6.1 Flex 规则摘要

```flex
"skip"      { return SKIP; }       /* skip 关键字 */
"if"        { return IF; }         /* if 关键字 */
"then"      { return THEN; }       /* then 关键字 */
"else"      { return ELSE; }       /* else 关键字 */
"while"     { return WHILE; }      /* while 关键字 */
"do"        { return DO; }         /* do 关键字 */
"short"     { return SHORT; }      /* short 类型 */
"int"       { return INT; }        /* int 类型 */
"long"      { return LONG; }       /* long 类型 */
"="         { return ASSIGN; }     /* 赋值运算符 = */
"&&"        { return AND; }        /* 逻辑与 */
"||"        { return OR; }         /* 逻辑或 */
"!"         { return NOT; }        /* 逻辑非 */
"{"         { return LBRACE; }     /* 左花括号 */
"}"         { return RBRACE; }     /* 右花括号 */
[0-9]+      { return INT_LITERAL; } /* 整数字面量 */
[a-zA-Z_][a-zA-Z0-9_]* { return IDENT; }  /* 标识符 */
```

### 6.2 特殊处理

- `long long` 作为单个 token 处理（通过正则匹配空白）
- 行号跟踪（`%option yylineno`）
- 注释跳过（`#.*`）

---

## 7. 语法分析实现

### 7.1 优先级与结合性

```bison
%left OR                    /* || */
%left AND                   /* && */
%left EQ NEQ                /* == != */
%left LT GT LE GE           /* < > <= >= */
%left PLUS MINUS            /* + - */
%left STAR SLASH MOD        /* * / % */
%right NOT                  /* ! */
%right CAST UNARY           /* (type) - * & */
```

### 7.2 语法结构

使用大括号包裹语句块：

```ebnf
if_stmt    ::= 'if' '(' expr ')' 'then' '{' commands '}' 'else' '{' commands '}'
while_stmt ::= 'while' '(' expr ')' 'do' '{' commands '}'
deref_assign ::= '*' expr '=' expr   /* 解引用赋值 */
```

### 7.3 语义动作

每个规则的语义动作负责构建对应的 AST 节点：

```bison
expr:
    expr PLUS term  { $$ = ast_binop(BIN_ADD, $1, $3); }
  | expr AND expr   { $$ = ast_binop(BIN_AND, $1, $3); }
  | NOT expr        { $$ = ast_not($2); }
```

---

## 8. 工具程序

### 8.1 ast_pretty

AST 格式化输出工具，用于调试和验证：

```bash
echo "int x; x = 5" | ./build/bin/ast_pretty
# 输出:
# int x;
# x = 5;
```

---

## 9. 测试策略

### 9.1 测试分类

- **正确性测试** (`test_*.wd`)：期望编译成功
- **错误检测测试** (`err_*.wd`)：期望编译失败并报错

### 9.2 自动化测试

`run_tests.sh` 脚本自动执行所有测试并验证结果：
- 正确性测试检查返回码为 0
- 错误测试检查返回码非 0

---

## 10. 已知限制

1. **无代码生成**：仅实现前端分析，不生成目标代码
2. **单文件编译**：不支持多文件或模块
3. **无数组类型**：仅支持标量和指针
4. **无函数**：不支持函数定义或调用
5. **错误恢复有限**：遇到第一个错误即终止

