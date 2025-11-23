# 带类型 WhileD 语言文法与规则

## 语言文法

### 完整 BNF 文法

```ebnf
program    ::= commands

commands   ::= command
            |  commands ';' command

command    ::= var_decl
            |  assignment
            |  while_loop
            |  if_then
            |  skip

var_decl   ::= type var_name

type       ::= base_type
            |  type '*'

base_type  ::= 'short' | 'int' | 'long' | 'long long'

assignment ::= ident ':=' expression

while_loop ::= 'while' expression 'do' commands 'od'

if_then    ::= 'if' expression 'then' commands 'else' commands 'fi'

expression ::= term
            |  expression '+' term
            |  expression '-' term

term       ::= factor
            |  term '*' factor
            |  term '/' factor
            |  term '%' factor

factor     ::= number
            |  ident
            |  '(' expression ')'
            |  '(' type ')' factor          # 显式类型转换
            |  '*' factor                    # 解引用
            |  '&' ident                     # 取地址
            |  '-' factor                    # 取反

number     ::= DIGIT+

ident      ::= LETTER (LETTER | DIGIT | '_')*

skip       ::= 'skip'
```

## 类型系统

### 支持的基本类型

- `short`（通常 16 位）
- `int`（通常 32 位）
- `long`（通常 32 或 64 位）
- `long long`（通常 64 位）
- 指针类型：`T*`，其中 T 可以是任何类型（包括指针）
- 多重指针：`int**`、`int***` 等

### 类型等级

从低到高：`short < int < long < long long`

## 隐式类型转换规则

### 一般原则

1. **常数提升规则**
   - 类型为 `short` 的常数自动提升为 `int`
   - 超出 `int` 范围的常数类型为 `long`
   - 超出 `long` 范围的常数类型为 `long long`

2. **二元运算符转换**
   - 如果操作数类型不同，将较低等级的类型转换为较高等级
   - 例如：`int + long` → `long + long`

3. **赋值转换**
   - 右值自动转换为左值的类型
   - 指针赋值要求类型兼容（指针与指针可相互赋值）

4. **函数调用转换**（暂不支持）

### 具体转换规则

| 源类型 | 目标类型 | 规则 |
|--------|--------|------|
| short | int | 允许 |
| short | long | 允许 |
| short | long long | 允许 |
| int | long | 允许 |
| int | long long | 允许 |
| long | long long | 允许 |
| 反向 | 任意 | 错误（可选警告） |

## 类型检查规则

### 操作数检查

#### 算术运算

- `+`、`-`、`*`、`/`、`%` 只能用于整数类型
- **不允许**指针类型参与算术运算
- **不允许**不同类别类型的混合运算

#### 指针运算

- 指针**不能**相加：`int *p, *q; p + q;` ❌
- 指针**不能**相乘、相除、相模
- 指针可以与整数相加/相减（地址算术，暂不完全支持）

#### 解引用操作

- 解引用 `*expr` 要求 `expr` 是指针类型
- `*non_pointer;` ❌ 错误
- 多重解引用 `**pp` 要求 `pp` 是指针的指针

#### 取地址操作

- 取地址 `&expr` 要求 `expr` 是**左值**（变量）
- `&(a + b);` ❌ 错误
- `&x;` ✓ 正确

### 赋值检查

- 变量必须在使用前声明
- 赋值类型必须兼容（整数赋给整数，指针赋给指针）
- 赋值不能将指针赋给非指针类型

### 作用域与声明

- 所有变量必须**先声明后使用**
- 同一作用域内不允许**重复声明**
- 支持嵌套块作用域（后续扩展）

## 错误处理

### 词法错误

- 非法字符
- 非法数字格式

### 语法错误

- 缺少分号
- 括号不匹配
- 关键字拼写错误

### 语义错误

- 变量未声明
- 变量重复声明
- 类型不兼容
- 类型转换非法
- 指针操作非法

## 示例

### 类型转换示例

```whiled
int x;
long y;
x := 5;
y := x;           # 隐式转换：int -> long
x := (int) y;     # 显式转换：long -> int
```

### 指针示例

```whiled
int* p;
int** pp;
int x;
p := &x;          # p 指向 x
pp := &p;         # pp 是 p 的地址
```

### 错误示例

```whiled
int *p;
int *q;
int z;
z := p + q;       # ❌ 指针不能相加

int *r;
z := *r;          # ❌ 解引用未初始化的指针（语义错误）

z := &(x + 1);    # ❌ 取地址非左值

int y;
y := &y;          # ❌ 地址赋给非指针类型
```
