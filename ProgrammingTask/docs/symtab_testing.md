# 符号表模块测试文档

本文档详细介绍了符号表模块 (`src/symtab.c`) 的测试策略、测试用例设计以及如何运行测试。

## 1. 测试概述

符号表是编译器的核心数据结构，负责管理变量的作用域、类型和生命周期。为了确保其正确性，我们编写了独立的单元测试 `tests/test_symtab_unit.c`，不依赖于词法或语法分析器，直接验证符号表的 API 行为。

## 2. 测试环境与运行

### 编译与运行命令

在 `ProgrammingTask` 目录下执行以下命令：

```bash
gcc -Iinclude -o build/test_symtab_unit tests/test_symtab_unit.c src/symtab.c src/type.c src/util.c && ./build/test_symtab_unit
```

### 预期输出

如果测试通过，终端将输出：

```text
Running test_basic_insert_lookup...
PASS
Running test_scope_shadowing...
PASS
Running test_duplicate_insert...
PASS
Running test_multi_level_nesting...
PASS
Running test_sibling_scopes...
PASS
All symtab tests passed!
```

## 3. 测试用例详解

我们设计了 5 个关键测试用例，覆盖了符号表的所有核心功能。

### 3.1 基础插入与查找 (`test_basic_insert_lookup`)
- **目标**: 验证在单一作用域内插入和查找变量的基本功能。
- **步骤**:
    1. 创建一个新作用域。
    2. 插入变量 `x` (int)。
    3. 验证 `lookup("x")` 返回正确符号。
    4. 验证 `lookup("y")` 返回 NULL。
- **意义**: 确保最基本的增删查改功能正常。

### 3.2 作用域遮蔽 (`test_scope_shadowing`)
- **目标**: 验证内层作用域变量遮蔽外层同名变量（Shadowing）。
- **步骤**:
    1. 全局作用域定义 `x` (int)。
    2. 进入子作用域，定义 `x` (long)。
    3. 在子作用域查 `x`，应为 `long`。
    4. 退出子作用域，查 `x`，应恢复为 `int`。
- **意义**: 验证嵌套代码块（如函数内的局部变量）能否正确覆盖全局变量。

### 3.3 重复定义检测 (`test_duplicate_insert`)
- **目标**: 验证同一作用域内不允许重复定义变量。
- **步骤**:
    1. 插入 `x`。
    2. 再次插入 `x`。
    3. 验证第二次插入返回 `false`。
- **意义**: 对应编译错误 "Redefinition of variable 'x'"。

### 3.4 多层嵌套测试 (`test_multi_level_nesting`)
- **目标**: 验证多层（3层以上）作用域链的查找逻辑。
- **结构**: `Global (L0) -> Mid (L1) -> Inner (L2)`
- **验证点**:
    - L2 能看到 L1 和 L0 的变量。
    - L1 能看到 L0 的变量，但看不见 L2 的。
    - L0 看不见 L1 和 L2 的变量。
- **意义**: 确保深层嵌套的代码块（如多重循环）能正确访问外部变量。

### 3.5 兄弟作用域隔离 (`test_sibling_scopes`)
- **目标**: 验证并列的代码块之间变量互不可见。
- **场景**:
    ```c
    // Parent
    int x;
    if (cond) {
        int y; // Sibling 1
    } else {
        int z; // Sibling 2
        // 这里应该能看见 x 和 z，但看不见 y
    }
    ```
- **验证点**: Sibling 2 查找 `y` 应该返回 NULL。
- **意义**: 确保 `if` 分支定义的变量不会泄漏到 `else` 分支。

## 4. 代码结构参考

- **测试源码**: `tests/test_symtab_unit.c`
- **实现源码**: `src/symtab.c`
- **头文件**: `include/symtab.h`
