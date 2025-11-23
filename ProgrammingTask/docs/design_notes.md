# 设计决策与实现说明

## 抽象语法树设计

### 两层 AST 模型

该实现采用**两层 AST** 模型：

1. **原始 AST** (`ast_t`)
   - 直接从语法分析得到
   - 不包含任何隐式类型转换信息
   - 用于错误报告和调试

2. **带类型的 AST** (`ast_typed_t`)
   - 在语义分析阶段生成
   - 每个表达式节点附带类型信息
   - 包含所有隐式 cast 节点

### 核心数据结构

```c
typedef struct ast_node {
    enum node_type type;
    union {
        struct { char* name; } var;
        struct { long value; } num;
        struct { struct ast_node* expr; } unop;
        struct { struct ast_node* left; struct ast_node* right; } binop;
        // ... 其他节点类型
    } data;
} ast_t;

typedef struct {
    ast_t* original;        // 原始 AST 节点指针
    type_t* inferred_type;  // 推断的类型
    ast_typed_t** children; // 类型化的子节点
} ast_typed_t;
```

## 符号表设计

### 分层符号表

使用**符号表栈**支持作用域：

```c
typedef struct symbol {
    char* name;
    type_t* type;
    int is_initialized;
} symbol_t;

typedef struct scope {
    symbol_t** symbols;
    int count;
    struct scope* parent;   // 链接到外层作用域
} scope_t;
```

### 符号表操作

- `symtab_push_scope()` - 进入新作用域
- `symtab_pop_scope()` - 退出作用域
- `symtab_insert()` - 插入符号（检查重复）
- `symtab_lookup()` - 查找符号（向上搜索）

## 类型检查算法

### 推断与验证

1. **自底向上推断**
   - 从表达式的叶子节点开始推断类型
   - 对于二元操作，结合两个操作数的类型

2. **验证规则应用**
   - 检查操作符与操作数类型的兼容性
   - 标记需要隐式类型转换的位置

3. **生成转换后的 AST**
   - 在需要的位置插入 `cast` 节点
   - 保留原始节点用于错误报告

### 类型转换示例

```c
// 原始 AST: int x; long y; x + y;
// 推断过程:
//   1. x 的类型 = int
//   2. y 的类型 = long
//   3. + 操作：int + long → 需要将 int 提升至 long
// 结果 AST: cast(x, int->long) + y
```

## 错误恢复

### 设计原则

- **单遍编译**：词法分析 → 语法分析 → 语义分析
- **前向错误恢复**（目前基础实现）
- 遇到错误时输出错误信息并继续分析（如果可能）

### 错误信息格式

```
error: <行号>:<列号>: <错误信息>
  | <源代码行>
  | ^^^ 
```

## 已知限制

1. ❌ **不支持**函数定义和调用
2. ❌ **不支持**数组类型
3. ❌ **不支持**结构体和联合体
4. ❌ **不支持**复合赋值（`+=`, `-=` 等）
5. ⚠️ **指针算术**仅部分支持（暂不计算偏移量）
6. ⚠️ **无循环优化**

## 后续扩展计划

1. 📋 **中间代码生成** (IR)
2. 📋 **代码优化** (常数折叠、死代码消除)
3. 📋 **机器代码生成**
4. 📋 **运行时支持** (标准库)

## 测试策略

### 单元测试

- 词法分析：测试各种 token 识别
- 类型系统：测试类型比较、转换规则
- 符号表：测试作用域、查找、插入

### 集成测试

- 完整程序编译
- 类型检查结果验证
- 错误报告准确性

### 回归测试

- 确保修改不破坏现有功能
- 维护测试用例库

## 性能考虑

- 符号表使用哈希表加速查找（可选）
- 内存池管理 AST 节点减少分配开销
- 一次性遍历 AST 进行语义分析

## 构建配置

### CMake 好处

- 跨平台支持（Windows/Linux/macOS）
- 自动依赖管理（flex/bison）
- 便于集成测试

### Makefile 好处

- 快速本地编译
- 无外部依赖
- 便于学习和调试

## 编码规范

- **命名**：`snake_case` 用于变量和函数，`UPPER_CASE` 用于宏
- **缩进**：4 个空格
- **注释**：详细注释复杂算法，简洁注释明显代码
- **错误处理**：检查所有指针和函数返回值

