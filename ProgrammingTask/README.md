# 带类型 WhileD 语言编译器

本项目实现了带类型 WhileD 语言的**词法分析**、**语法分析**和**类型分析**。

## 项目概述

### 支持的语言特性

#### 基本语法
- WhileD 语言的完整语法（赋值、条件、循环）
- 带类型的变量声明：`type var_name; command`
- 显式类型转换：`(type) expression`

#### 支持的类型
| 类型 | 说明 |
|------|------|
| `short` | 短整型 |
| `int` | 整型 |
| `long` | 长整型 |
| `long long` | 长长整型 |
| `T*` | 指针类型（支持多级指针如 `int**`、`int***`） |

#### 核心功能
- 词法分析（基于 Flex）
- 语法分析（基于 Bison）
- 符号表管理与作用域处理
- 类型检查（变量先声明后使用）
- 隐式类型转换推断
- 详细的错误报告

## 目录结构

```
ProgrammingTask/
├── README.md                 # 本文件
├── Makefile                  # 构建配置
├── docs/                     # 文档
│   ├── language_spec.md      # 语言规范与类型规则
│   └── design_notes.md       # 设计说明
├── examples/                 # 示例程序
├── tests/                    # 测试用例
│   ├── cases/                # 测试源文件
│   └── run_tests.sh          # 测试脚本
├── include/                  # 头文件
├── src/                      # 源代码
├── tools/                    # 工具程序
└── build/                    # 构建输出
```

## 构建与运行

### 依赖要求

- GCC（支持 C99）
- Flex（词法分析器生成器）
- Bison（语法分析器生成器）
- GNU Make

### 编译

```bash
cd ProgrammingTask
make
```

生成的可执行文件：
- `build/bin/whiled` - 主编译器
- `build/bin/ast_pretty` - AST 格式化工具

### 运行

```bash
# 编译 WhileD 源文件
./build/bin/whiled examples/simple_decl.wd

# 查看 AST 结构
./build/bin/ast_pretty examples/simple_decl.wd
```

### 运行测试

```bash
# 运行全部测试
./tests/run_tests.sh

# 显示详细输出
./tests/run_tests.sh -v
```

## 使用示例

### 基本程序

```whiled
int x;
x = 5;
int y;
y = x + 10;
while (y > 0) do {
    y = y - 1
}
```

### 指针操作

```whiled
int x;
x = 42;
int* p;
p = &x;
int y;
y = *p
```

### 类型转换

```whiled
short s;
s = 10;
int i;
i = s;           # 隐式转换：short → int
long l;
l = (long) i     # 显式转换：int → long
```

## 文档

详细说明请参阅 `docs/` 目录：

- [语言规范](docs/language_spec.md) - 完整的语法和类型规则
- [设计说明](docs/design_notes.md) - 实现细节和设计决策

## 测试用例

测试用例位于 `tests/cases/` 目录：

### 正确性测试（应通过编译）
| 文件 | 测试内容 |
|------|----------|
| `test_basic_types.wd` | 基本类型声明 |
| `test_pointer_basic.wd` | 基本指针操作 |
| `test_pointer_to_pointer.wd` | 多级指针 |
| `test_cast_explicit.wd` | 显式类型转换 |
| `test_implicit_conversion.wd` | 隐式类型转换 |
| `test_arithmetic_ops.wd` | 算术运算 |
| `test_comparison_ops.wd` | 比较运算 |
| `test_if_else.wd` | 条件语句 |
| `test_while_loop.wd` | 循环语句 |
| `test_unary_minus.wd` | 一元负号 |
| `test_nested_scope.wd` | 嵌套作用域 |

### 错误检测测试（应报错）
| 文件 | 测试的错误 |
|------|-----------|
| `err_undefined_var.wd` | 使用未声明变量 |
| `err_pointer_add.wd` | 指针相加（非法） |
| `err_deref_nonptr.wd` | 解引用非指针 |
| `err_pointer_mul.wd` | 指针参与乘法（非法） |
| `err_unary_minus_ptr.wd` | 对指针取负（非法） |
| `err_addr_rvalue.wd` | 类型不匹配赋值 |
