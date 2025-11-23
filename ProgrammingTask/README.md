# 带类型 WhileD 编译器 - ProgrammingTask

一个支持类型检查和隐式类型转换的 WhileD 语言编译器实现。这是大作业的第一个任务。

## 任务要求

带类型 WhileD 语言需要支持：

### 基本语法
- 所有原生 WhileD 语言的语法
- 带类型的变量声明：`type_name var_name; command`
- 显式类型转换：`(type_name) expression`

### 支持的类型
- 基本类型：`short`、`int`、`long`、`long long`
- 指针类型：`T*`、`T**`、`T***` 等（多重指针）

### 核心功能
- 完整的词法分析（使用 Flex）
- 递归下降语法分析（使用 Bison）
- 符号表管理和作用域处理
- 类型检查（变量先声明后使用）
- 隐式类型转换的自动推断
- 详细的错误报告

## 目录结构

```
.
├── CMakeLists.txt           # CMake 构建配置
├── Makefile                 # Makefile 构建（快速编译）
├── .gitignore               # Git 忽略文件
├── README.md                # 本文件
├── docs/                    # 文档
│   ├── language_spec.md     # 语言文法与规则
│   ├── design_notes.md      # 设计决策与限制
│   └── examples.md          # 示例说明
├── examples/                # 示例程序
│   ├── simple_decl.wd
│   ├── pointers.wd
│   └── type_errors.wd
├── tests/                   # 测试用例
│   ├── cases/               # 测试源文件
│   ├── expected/            # 预期输出
│   └── run_tests.sh         # 测试运行脚本
├── include/                 # 头文件
│   ├── ast.h
│   ├── type.h
│   ├── symtab.h
│   ├── lexer.h
│   ├── parser.h
│   └── util.h
├── src/                     # 源文件
│   ├── main.c               # 程序入口
│   ├── driver.c             # 编译驱动
│   ├── lexer.l              # Flex 词法规则
│   ├── parser.y             # Bison 文法
│   ├── ast.c                # 抽象语法树
│   ├── type.c               # 类型系统
│   ├── symtab.c             # 符号表
│   ├── analyze.c            # 语义分析
│   ├── ast_printer.c        # AST 打印
│   └── util.c               # 工具函数
├── tools/                   # 工具程序
│   └── ast_pretty.c         # AST 格式化工具
├── build/                   # 构建输出目录
└── scripts/                 # 脚本
    ├── format.sh            # 代码格式化
    └── gen_parser.sh        # 生成解析器
```

## 构建与运行

### 依赖要求

- C99 编译器（gcc/clang/msvc）
- Flex 词法分析器生成器
- Bison 语法分析器生成器
- CMake 3.10+ 或 GNU Make

### 方法一：使用 Makefile（快速开发）

```bash
# 在 ProgrammingTask 目录中执行

# 构建项目
make

# 清理构建产物
make clean

# 显示帮助
make help
```

**输出位置**：`build/bin/whiled` 和 `build/bin/ast_pretty`

### 方法二：从根目录使用 Makefile

```bash
# 在项目根目录执行

# 构建 ProgrammingTask
make programming-task

# 清理 ProgrammingTask
make clean
```

### 方法三：使用 CMake

**从根目录**：
```bash
mkdir build && cd build
cmake ..
cmake --build .
```

**或在 ProgrammingTask 目录**：
```bash
mkdir build && cd build
cmake ..
cmake --build .
```

## 使用示例

### 编译和运行编译器

```bash
# 分析一个 WhileD 程序文件
./build/bin/whiled examples/simple_decl.wd

# 使用 AST 打印工具（用于调试）
./build/bin/ast_pretty examples/simple_decl.wd
```

### 运行测试

```bash
cd tests
bash run_tests.sh              # 运行所有测试
bash run_tests.sh --verbose    # 显示详细输出
```

### 示例程序

查看 `examples/` 目录中的示例：

- `simple_decl.wd` - 基本的变量声明和赋值
- `pointers.wd` - 指针操作
- `type_errors.wd` - 类型错误示例

## 语言特性

### 基本语法

```
int x;
x := 5;
while x > 0 do
  x := x - 1
od
```

### 类型声明

```
short s;
int i;
long l;
long long ll;
int* p;           # int 指针
int** pp;         # int 指针的指针
```

### 类型转换

```
int x;
long y;
x := (int) y;     # 显式转换
y := x;           # 隐式转换（int -> long）
```

## 文档

详见 `docs/` 目录的详细文档：

- **[language_spec.md](docs/language_spec.md)** 
  - 完整的 BNF 文法
  - 类型系统规范
  - 隐式类型转换规则
  - 类型检查规则

- **[design_notes.md](docs/design_notes.md)**
  - 抽象语法树设计
  - 符号表设计
  - 类型检查算法
  - 已知限制和后续扩展计划

- **[examples.md](docs/examples.md)**
  - 基础示例
  - 类型转换示例
  - 错误示例
  - 复杂示例

## 根目录信息

项目级别的说明请见 [`../README.md`](../README.md)，包括：
- 整个多任务项目的结构
- 全局构建系统的使用
- 如何添加新任务
