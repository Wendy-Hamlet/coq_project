# 程序语言与编译原理大作业

## 项目概述

本项目为**程序语言与编译原理**课程的大作业，包含以下任务：

- **ProgrammingTask** - 带类型 WhileD 语言的词法分析、语法分析和类型分析

## 目录结构

```
coq_project/
├── README.md                  # 本文件
├── Makefile                   # 构建配置
├── Projects.pdf               # 作业要求文档
│
└── ProgrammingTask/           # 编程任务：WhileD 编译器
    ├── README.md              # 任务说明
    ├── Makefile               # 任务构建配置
    ├── docs/                  # 文档
    │   ├── language_spec.md   # 语言规范
    │   └── design_notes.md    # 设计说明
    ├── examples/              # 示例程序
    ├── tests/                 # 测试用例
    ├── include/               # 头文件
    ├── src/                   # 源代码
    ├── tools/                 # 工具程序
    └── build/                 # 构建输出
```

## 构建与运行

### 依赖要求

- GCC（支持 C99）
- Flex（词法分析器生成器）
- Bison（语法分析器生成器）
- GNU Make

### 编译

```bash
# 在根目录构建
make

# 或进入任务目录构建
cd ProgrammingTask
make
```

### 运行

```bash
# 编译 WhileD 程序
./ProgrammingTask/build/bin/whiled ProgrammingTask/examples/simple_decl.wd

# 查看 AST
./ProgrammingTask/build/bin/ast_pretty ProgrammingTask/examples/simple_decl.wd
```

### 测试

```bash
cd ProgrammingTask/tests
bash run_tests.sh
```

## 文档

详细文档请参阅：
- [ProgrammingTask/README.md](ProgrammingTask/README.md) - 任务说明
- [ProgrammingTask/docs/language_spec.md](ProgrammingTask/docs/language_spec.md) - 语言规范
- [ProgrammingTask/docs/design_notes.md](ProgrammingTask/docs/design_notes.md) - 设计说明
