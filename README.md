# 程序语言与编译原理大作业

## 项目概述

该项目包含以下主要任务：

- **ProgrammingTask** - 带类型 WhileD 语言的词法分析、语法分析和类型分析

理论作业待添加。

## 目录结构

```
coq_project/                    # Git 根目录
├── CMakeLists.txt             # 主项目配置（管理所有子项目）
├── Makefile                   # 根目录 Makefile（统一构建入口）
├── .gitignore                 # Git 忽略规则
├── README.md                  # 本文件：项目级说明与构建指南
├── Projects.pdf               # 作业要求文档
│
├── ProgrammingTask/           # 第一个任务：WhileD 编译器
│   ├── CMakeLists.txt         # 子项目配置
│   ├── Makefile               # 任务级 Makefile
│   ├── README.md              # 任务说明：具体功能、语言特性
│   ├── docs/                  # 文档
│   │   ├── language_spec.md   # 语言文法、类型规则
│   │   ├── design_notes.md    # 设计决策、限制说明
│   │   └── examples.md        # 使用示例和测试用例
│   ├── examples/              # 示例程序
│   ├── tests/                 # 测试用例
│   ├── include/               # 头文件
│   ├── src/                   # 源代码
│   ├── tools/                 # 工具程序
│   ├── build/                 # 构建输出
│   └── scripts/               # 构建脚本
│
# 后续任务添加到这里...
```

## 构建与运行

### 依赖要求

- **C99 编译器**：gcc、clang 或 MSVC
- **Flex**：词法分析器生成器
- **Bison**：语法分析器生成器
- **CMake 3.10+**（如果使用 CMake）
- **GNU Make**（如果使用 Makefile）

### 方法一：使用根目录 Makefile

从项目根目录执行：

```bash
# 构建所有任务
make

# 只构建 ProgrammingTask
make programming-task

# 清理所有构建产物
make clean

# 显示帮助信息
make help
```

**输出位置**：
```
ProgrammingTask/build/bin/whiled         # 主程序
ProgrammingTask/build/bin/ast_pretty     # 工具程序
```

### 方法二：使用 ProgrammingTask 中的 Makefile

进入任务目录后执行：

```bash
cd ProgrammingTask

# 构建项目
make

# 清理产物
make clean

# 帮助
make help
```

### 方法三：使用 CMake

从项目根目录执行：

```bash
# 创建并进入构建目录
mkdir build
cd build

# 配置项目
cmake ..

# 构建所有目标
cmake --build .

# 或在 Linux/macOS 上
make -j4
```

**输出位置**：
```
build/bin/whiled         # 主程序
build/bin/ast_pretty     # 工具程序
```

### 使用编译器

```bash
# 分析一个 WhileD 程序
./ProgrammingTask/build/bin/whiled ProgrammingTask/examples/simple_decl.wd

# 使用 AST 打印工具
./ProgrammingTask/build/bin/ast_pretty ProgrammingTask/examples/simple_decl.wd
```

## 快速开始

### 第一次完整构建

```bash
# 1. 在根目录构建所有任务
make

# 2. 运行测试
cd ProgrammingTask
cd tests
bash run_tests.sh

# 3. 尝试示例
../build/bin/whiled ../examples/simple_decl.wd
```

### 日常开发流程

```bash
# 修改代码后重新构建
cd ProgrammingTask
make

# 清理旧文件
make clean
```

## 文档指引

详见 `ProgrammingTask/` 中的文档：
- [`docs/language_spec.md`](ProgrammingTask/docs/language_spec.md) - 语言文法和类型规则
- [`docs/design_notes.md`](ProgrammingTask/docs/design_notes.md) - 设计决策和限制
- [`docs/examples.md`](ProgrammingTask/docs/examples.md) - 使用示例和测试用例


```
ProgrammingTask/                    # 项目根
├─ CMakeLists.txt                # 或 Makefile（建议用 CMake 或简单 Makefile）
├─ README.md                     # 项目说明、构建与运行步骤
├─ LICENSE
├─ docs/
│  ├─ language_spec.md           # 语言文法、类型规则与转换规则（提交文档的一部分）
│  ├─ design_notes.md            # 设计决策、已知限制、测试计划
│  └─ examples.md                # 例子说明与测试用例说明
├─ examples/                     # 示例源程序（用于测试）
│  ├─ simple_decl.wd
│  ├─ pointers.wd
│  └─ type_errors.wd
├─ tests/                        # 自动化测试用例（脚本 + 输入输出）
│  ├─ run_tests.sh
│  ├─ cases/
│  │  ├─ 01-decl-and-assign.wd
│  │  ├─ 02-pointer-arith.wd
│  │  └─ ...
│  └─ expected/                  # 对应预期输出 / 错误消息
├─ tools/                        # 小工具（例如 AST pretty-printer、dump AST json）
│  └─ ast_pretty.c
├─ include/                      # 公共头文件
│  ├─ ast.h
│  ├─ type.h
│  ├─ symtab.h
│  ├─ lexer.h
│  ├─ parser.h
│  └─ util.h
├─ src/                          # 源代码
│  ├─ main.c                     # CLI：读取文件/字符串，驱动词法/语法/语义分析
│  ├─ driver.c                   # 编译驱动：构建 AST、调用分析器、打印结果
│  ├─ lexer.l                    # flex 词法规则
│  ├─ parser.y                   # bison 文法（生成 parser.c/h）
│  ├─ ast.c                      # AST 节点构造/销毁/遍历辅助函数
│  ├─ type.c                     # Type 结构、比较、复制、常用判断函数（is_integer/is_pointer）
│  ├─ symtab.c                   # 符号表、作用域 push/pop、查找/插入
│  ├─ analyze.c                  # 语义分析：类型推断、检查、隐式 cast 插入（核心）
│  ├─ transform_casts.c          # 可选：将隐式 cast 插入逻辑单独模块化
│  ├─ ast_printer.c              # AST -> 可读文本（便于调试）
│  └─ util.c                     # 错误/位置处理、内存管理、字符串工具
├─ build/                        # 构建输出（CMake 默认或 Makefile 输出目录）
└─ scripts/
   ├─ format.sh                  # 代码格式化脚本（可选）
   └─ gen_parser.sh              # 生成 parser/lexer 的脚本（flex+bison 调用）
'''