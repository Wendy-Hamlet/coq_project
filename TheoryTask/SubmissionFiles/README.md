# 验证文件提交目录

本目录包含用于课程验证的所有关键文件，便于检查和评审。

## 文件列表

### C 源代码与规约（3个文件）

| 文件 | 说明 |
|------|------|
| `sll_project_def.h` | C 数据结构定义与 Coq 谓词声明 |
| `sll_project_lib.c` | C 函数实现及形式化规约（包含 `Require`/`Ensure`/`With`/`Inv` 注释） |
| `sll_project.strategies` | 93 个策略规则定义 |

### Coq 验证文件（8个文件）

| 文件 | 说明 | 类型 |
|------|------|------|
| `sll_project_lib.v` | 分离逻辑谓词定义与核心引理 | 手动编写 |
| `sll_project_strategy_goal.v` | 策略验证目标 | 自动生成 |
| `sll_project_strategy_goal_check.v` | 策略目标一致性检查 | 自动生成 |
| `sll_project_strategy_proof.v` | 策略正确性证明 | 手动完成 |
| `sll_project_goal.v` | C 函数验证目标 | 自动生成 |
| `sll_project_goal_check.v` | 函数目标一致性检查 | 自动生成 |
| `sll_project_proof_auto.v` | 自动生成的证明框架 | 自动生成 |
| `sll_project_proof_manual.v` | 核心函数手动证明 | 手动完成 |

## 文件来源

这些文件从项目的以下位置复制：

- **C 源代码**：`qcp-binary-democases/QCP_examples/`
- **Coq 文件**：`qcp-binary-democases/SeparationLogic/examples/`

## 更新方法

运行构建脚本后会自动更新本目录：

```bash
# Linux/macOS/WSL
./build.sh

# Windows
.\build.bat
```

或手动执行：

```bash
# Linux/macOS/WSL
./copy_submission_files.sh

# Windows
.\copy_submission_files.ps1
```

## 验证完整性

所有文件应该都能通过 Coq 编译：

```bash
cd ../qcp-binary-democases/SeparationLogic
make
```

如果编译成功，说明所有证明都已完成且正确。
