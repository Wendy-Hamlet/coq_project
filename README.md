# 程序语言与编译原理大作业

## 项目概述

本项目为**程序语言与编译原理**课程的大作业，包含编程任务和理论任务两部分：

- **ProgrammingTask** - 带类型 WhileD 语言的词法分析、语法分析和类型分析
- **TheoryTask** - 基于 Coq 的链表数据结构形式化验证

## 目录结构

```
coq_project/
├── README.md                   # 本文件
├── Makefile                    # 构建配置
│
├── ProgrammingTask/            # 编程任务：WhileD 编译器
│   ├── README.md               # 任务说明
│   ├── Makefile                # 构建配置
│   ├── docs/                   # 文档
│   │   ├── language_spec.md    # 语言规范
│   │   └── design_notes.md     # 设计说明
│   ├── examples/               # 示例程序
│   ├── tests/                  # 测试用例
│   ├── include/                # 头文件
│   ├── src/                    # 源代码
│   ├── tools/                  # 工具程序
│   └── build/                  # 构建输出
│
└── TheoryTask/                 # 理论任务：Coq 形式化验证
    ├── README.md               # 任务说明
    ├── Makefile                # 构建配置
    ├── _CoqProject             # Coq 项目配置
    ├── pl/                     # 程序语言基础库
    ├── sets/                   # 集合论库
    ├── comcert_lib/            # CompCert 库
    ├── SubmissionFiles/        # 提交文件汇总（包含所有关键验证文件）
    │   ├── README.md           # 文件说明
    │   ├── sll_project_def.h   # C 数据结构定义
    │   ├── sll_project_lib.c   # C 函数实现
    │   ├── sll_project.strategies # 策略规则定义
    │   └── *.v                 # 8个 Coq 验证文件
    └── qcp-binary-democases/   # QCP 验证工具与示例
        ├── QCP_examples/       # C 源代码与形式化规约
        │   ├── sll_project_def.h        # 数据结构定义与 Coq 谓词声明
        │   ├── sll_project_lib.c        # C 函数实现及规约注释
        │   └── sll_project.strategies   # 策略规则定义
        └── SeparationLogic/
            └── examples/       # Coq 验证文件
                ├── sll_project_lib.v                # 谓词定义与核心引理
                ├── sll_project_strategy_goal.v      # 策略验证目标
                ├── sll_project_strategy_goal_check.v # 策略目标检查
                ├── sll_project_strategy_proof.v     # 策略正确性证明
                ├── sll_project_goal.v               # C 函数验证目标
                ├── sll_project_goal_check.v         # 函数目标检查
                ├── sll_project_proof_auto.v         # 自动生成的证明框架
                └── sll_project_proof_manual.v       # 手动完成的核心证明
```

## 任务一：ProgrammingTask - WhileD 编译器

### 功能特性

- 基于 Flex 的词法分析
- 基于 Bison 的语法分析
- 符号表管理与作用域处理
- 类型检查与类型推断
- 支持多级指针、类型转换等高级特性

### 依赖要求

- GCC（支持 C99）
- Flex（词法分析器生成器）
- Bison（语法分析器生成器）
- GNU Make

### 构建与运行

```bash
# 进入任务目录
cd ProgrammingTask

# 编译
make

# 运行示例
./build/bin/whiled examples/example_1.wd

# 查看 AST
./build/bin/ast_pretty examples/example_1.wd

# 运行测试
./tests/run_tests.sh
```

### 文档

- [ProgrammingTask/README.md](ProgrammingTask/README.md) - 详细说明
- [ProgrammingTask/docs/language_spec.md](ProgrammingTask/docs/language_spec.md) - 语言规范
- [ProgrammingTask/docs/design_notes.md](ProgrammingTask/docs/design_notes.md) - 设计说明

## 任务二：TheoryTask - Coq 形式化验证

### 验证内容

本任务使用 Coq 证明助手和分离逻辑，对基于双重指针实现高效尾部操作的链表数据结构（List Box）进行形式化验证。

#### 核心数据结构

```c
struct sll {
    unsigned int data;
    struct sll * next;
};

struct sllb {
    struct sll * head;    // 链表头指针
    struct sll ** ptail;  // 指向尾部的双重指针
};
```

**设计思想**：`ptail` 是指向"下一个节点应该插入位置"的双重指针。对于空链表，它指向 `&head`；对于非空链表，它指向最后一个节点的 `&next` 字段。

#### 核心函数：链表合并

```c
struct sllb * app_list_box(struct sllb * b1, struct sllb * b2) {
    *(b1->ptail) = b2->head;      // 将 b2 的头连接到 b1 的尾部
    if (b2->head != NULL) {
        b1->ptail = b2->ptail;    // 更新 b1 的尾指针为 b2 的尾指针
    }
    free_sllb(b2);
    return b1;
}
```

该函数通过双重指针 `ptail` 实现常数时间的链表合并，是本项目的核心验证目标。

#### 验证任务与难度分级

根据课程要求，验证任务分为三个难度档次：

| 难度档次 | 验证函数 | 完成情况 |
|---------|---------|---------|
| **第二档** | `nil_list_box`、`cons_list_box`、`free_list_box`、`app_list_box` | ✅ 已完成 |
| **第三档** | 第二档 + `map_list_box` | ✅ 已完成 |
| **第四档** | 第三档 + `sllb2array` | ✅ 已完成 |

#### 已验证函数详细说明

**主要函数**：

| 函数 | 功能 | 验证状态 | 关键技术 |
|------|------|---------|---------|
| `nil_list_box()` | 创建空链表盒子 | ✅ 已验证 | 初始化 `ptail = &head` |
| `cons_list_box(data, box)` | 头部插入节点 | ✅ 已验证 | 区分空/非空情况更新 `ptail` |
| `free_list_box(box)` | 释放链表盒子 | ✅ 已验证 | 策略 32 自动展开 `sllb` |
| `app_list_box(b1, b2)` | 合并两个链表 | ✅ 已验证 | `sllbseg_append_sllbseg` 引理 |
| `map_list_box(box, x)` | 映射操作（乘法） | ✅ 已验证 | 策略 35/36 自动视图转换 |
| `sllb2array(box, arr)` | 转换为数组 | ✅ 已验证 | 策略 70-93 处理数组边界 |

**辅助函数**：

| 函数 | 功能 | 验证状态 |
|------|------|---------|
| `nil_list()` | 创建空链表 | ✅ 已验证 |
| `cons_list(data, next)` | 链表头部插入 | ✅ 已验证 |
| `free_list(head)` | 释放链表 | ✅ 已验证（含循环不变量） |
| `map_list(head, x)` | 映射操作（底层） | ✅ 已验证（含循环不变量） |
| `sll_length(head)` | 计算链表长度 | ✅ 已验证 |
| `sll2array(head, arr)` | 链表转数组（底层） | ✅ 已验证（含循环不变量） |

**未验证函数**（仅声明，无需验证）：
- `new_list_node()`、`new_sllb()`、`new_uint_array()`（内存分配）
- `free_list_node()`、`free_sllb()`（内存释放）

### 依赖要求

- Coq 8.20.1
- GNU Make

### 构建与验证

#### 第一步：环境搭建

```bash
# 1. 拉取最新代码
git pull

# 2. 初始化并更新子模块
git submodule update --init --recursive

# 3. 编译 unifysl 基础库
cd TheoryTask/qcp-binary-democases/SeparationLogic/unifysl/
make depend
make

# 4. 编译 SeparationLogic 库
cd ..
make depend
make

# 5. 返回项目根目录
cd ../../..
```

#### 第二步：生成验证文件（需要在 Cygwin/WSL/Linux/macOS 终端中执行）

```bash
# 进入 QCP 工具目录
cd TheoryTask/qcp-binary-democases

# 删除旧的生成文件（保留 sll_project_lib.v）
rm -f SeparationLogic/examples/sll_project_goal.v \
      SeparationLogic/examples/sll_project_goal_check.v \
      SeparationLogic/examples/sll_project_proof_auto.v \
      SeparationLogic/examples/sll_project_proof_manual.v \
      SeparationLogic/examples/sll_project_strategy_goal.v \
      SeparationLogic/examples/sll_project_strategy_goal_check.v \
      SeparationLogic/examples/sll_project_strategy_proof.v

# 生成 C 程序验证相关文件（4个）
win-binary/symexec.exe \
  --goal-file=SeparationLogic/examples/sll_project_goal.v \
  --proof-auto-file=SeparationLogic/examples/sll_project_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/sll_project_proof_manual.v \
  -I QCP_examples/ \
  -slp QCP_examples/ \
  SimpleC.EE \
  --input-file=QCP_examples/sll_project_lib.c \
  --no-exec-info

# 生成策略验证相关文件（3个）
win-binary/StrategyCheck.exe \
  --strategy-folder-path=SeparationLogic/examples/ \
  --coq-logic-path=SimpleC.EE \
  --input-file=QCP_examples/sll_project.strategies \
  --no-exec-info

# 编译生成的 Coq 文件
cd SeparationLogic
make depend
make

# 返回项目根目录
cd ../../../..
```

**注意事项**：
- Windows 用户：需要 Cygwin 或 WSL 环境
- macOS/Linux 用户：将 `win-binary/` 替换为 `mac-arm64-binary/` 或 `linux-binary/`
- 生成工具会产生一些无害的警告信息（如 `pipe: No such file or directory`）

#### 快速构建（使用自动化脚本）

**Windows 用户**：
```powershell
# 使用 PowerShell（需要手动运行验证文件生成步骤）
.\build.ps1

# 或使用批处理文件（自动检测 Cygwin/WSL）
.\build.bat

# 仅环境搭建，跳过验证文件生成
.\build.ps1 -SkipSetup:$false
```

**Linux/macOS/Cygwin/WSL 用户**：
```bash
# 完整构建
./build.sh

# 仅环境搭建
./build.sh --skip-setup

# 清理生成文件
./clean.sh
```

**脚本功能**：
- `build.sh` / `build.ps1`：自动执行环境搭建和验证文件生成
- `build.bat`：Windows 批处理包装器，自动检测 Cygwin/WSL
- `clean.sh`：清理生成的验证文件（保留 `sll_project_lib.v`）

### 验证要求

根据课程要求，需要完成以下工作：

1. **定义分离逻辑谓词**：精确刻画 `sllb` 结构在不同状态下的内存布局
2. **设计 Strategies**：为分离逻辑谓词设计必要的策略证明
3. **标注前后条件**：为 C 函数标注精确的前置条件和后置条件
4. **添加循环不变量**：为包含循环的函数添加必要的标注
5. **完成 Coq 证明**：在 Coq 中完成所有验证目标的证明

### 主要文件说明

**C 源代码与规约**（位于 `qcp-binary-democases/QCP_examples/`）：

| 文件 | 说明 |
|------|------|
| `sll_project_def.h` | C 数据结构定义与 Coq 谓词声明 |
| `sll_project_lib.c` | C 函数实现及形式化规约 |
| `sll_project.strategies` | 策略规则设计，处理谓词展开、匹配、数组操作等 |

**Coq 验证文件**（位于 `qcp-binary-democases/SeparationLogic/examples/`）：

| 文件 | 说明 |
|------|------|
| `sll_project_lib.v` | 分离逻辑谓词定义（`sll`、`sllb`、`sllb_sll`、`sllbseg`、`sll_pt` 等）及核心引理 |
| `sll_project_strategy_goal.v` | 策略验证目标（从 `.strategies` 文件生成） |
| `sll_project_strategy_proof.v` | 策略证明 |
| `sll_project_goal.v` | C 函数验证目标（从 `.c` 文件的注释生成） |
| `sll_project_proof_auto.v` | 自动生成的证明框架 |
| `sll_project_proof_manual.v` | 手动完成的证明 |
| `sll_project_goal_check.v` | 验证目标一致性检查 |

### 文档

- [TheoryTask/README.md](TheoryTask/README.md) - 详细验证说明
- [TheoryTask/sllb_lemmas_guide.md](TheoryTask/sllb_lemmas_guide.md) - 引理指南
- [TheoryTask/app_list_box_verification_notes.md](TheoryTask/app_list_box_verification_notes.md) - `app_list_box` 验证笔记
- [TheoryTask/sllb2array_verification_notes.md](TheoryTask/sllb2array_verification_notes.md) - `sllb2array` 验证笔记
- [TheoryTask/precision_problem_analysis.md](TheoryTask/precision_problem_analysis.md) - 精确性问题分析
## 提交文件说明

所有用于课程验证的关键文件已整理到 **[TheoryTask/SubmissionFiles/](TheoryTask/SubmissionFiles/)** 目录：

- **C 源代码**（3个）：`sll_project_def.h`, `sll_project_lib.c`, `sll_project.strategies`
- **Coq 验证文件**（8个）：包括手动编写的谓词定义、策略证明及自动生成的验证目标

详细说明请查看 [TheoryTask/SubmissionFiles/README.md](TheoryTask/SubmissionFiles/README.md)。构建脚本执行后会自动更新这些文件。