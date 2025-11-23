# 使用示例与测试用例

## 基础示例

### 1. 简单变量声明与赋值

**文件**: `simple_decl.wd`

```whiled
int x;
x := 5;
int y;
y := 10;
x := x + y
```

**预期输出**:
```
编译成功
变量声明: int x, int y
赋值: x = 5, y = 10, x = x + y
```

### 2. 多种类型

**文件**: `types.wd`

```whiled
short s;
int i;
long l;
long long ll;
s := 100;
i := 1000;
l := i;
ll := l
```

**预期输出**:
```
编译成功
类型推断:
  s: short
  i: int
  l: long (来自 int 的隐式转换)
  ll: long long (来自 long 的隐式转换)
```

### 3. 指针类型

**文件**: `pointers.wd`

```whiled
int x;
int* p;
int** pp;
x := 5;
p := &x;
pp := &p
```

**预期输出**:
```
编译成功
类型推断:
  x: int
  p: int*
  pp: int**
```

## 类型转换示例

### 4. 隐式类型提升

**文件**: `implicit_cast.wd`

```whiled
short s;
int i;
long l;
s := 10;
i := s;
l := i;
l := s
```

**预期输出**:
```
编译成功
隐式转换:
  line 4: short -> int
  line 5: int -> long  
  line 6: short -> long
```

### 5. 显式类型转换

**文件**: `explicit_cast.wd`

```whiled
int i;
long l;
i := 100;
l := i;
i := (int) l
```

**预期输出**:
```
编译成功
显式转换:
  line 5: long -> int
```

## 控制流示例

### 6. While 循环

**文件**: `while_loop.wd`

```whiled
int x;
x := 5;
while x > 0 do
  x := x - 1
od
```

**预期输出**:
```
编译成功
循环体类型检查通过
```

### 7. If-Then-Else

**文件**: `if_then.wd`

```whiled
int x;
x := 5;
if x > 0 then
  x := 1
else
  x := 0
fi
```

**预期输出**:
```
编译成功
条件分支类型检查通过
```

## 错误示例

### 8. 未声明变量 ❌

**文件**: `error_undeclared.wd`

```whiled
x := 5
```

**预期错误**:
```
error: line 1: 变量 'x' 未声明
```

### 9. 重复声明 ❌

**文件**: `error_redeclare.wd`

```whiled
int x;
int x;
x := 5
```

**预期错误**:
```
error: line 2: 变量 'x' 已声明
```

### 10. 类型不兼容 ❌

**文件**: `error_type_mismatch.wd`

```whiled
int* p;
int x;
p := x
```

**预期错误**:
```
error: line 3: 类型不兼容: int 不能赋给 int*
```

### 11. 指针运算错误 ❌

**文件**: `error_pointer_arith.wd`

```whiled
int* p;
int* q;
int r;
r := p + q
```

**预期错误**:
```
error: line 4: 指针类型不能参与加法运算
```

### 12. 解引用错误 ❌

**文件**: `error_deref.wd`

```whiled
int x;
int y;
y := *x
```

**预期错误**:
```
error: line 3: 只有指针类型可以解引用，x 的类型是 int
```

### 13. 取地址错误 ❌

**文件**: `error_address.wd`

```whiled
int x;
int* p;
p := &(x + 1)
```

**预期错误**:
```
error: line 3: 只能对左值进行取地址操作
```

## 复杂示例

### 14. 多指针操作

**文件**: `complex_pointers.wd`

```whiled
int x;
int* p;
int** pp;
int*** ppp;
x := 42;
p := &x;
pp := &p;
ppp := &pp
```

**预期输出**:
```
编译成功
多级指针类型检查通过
```

### 15. 混合运算与转换

**文件**: `complex_expr.wd`

```whiled
short s;
int i;
long l;
s := 5;
i := 10;
l := s + i;
l := (long)(s * i)
```

**预期输出**:
```
编译成功
隐式转换链:
  line 5: short + int -> int + int -> int
  line 6: 结果 int 转换为 long
  line 7: short * int -> int * int -> int, 显式转换为 long
```

## 测试运行方式

### 逐个测试

```bash
cd ProgrammingTask
make                              # 构建
./build/bin/whiled examples/simple_decl.wd
./build/bin/whiled examples/error_undeclared.wd
```

### 批量测试

```bash
cd tests
bash run_tests.sh
```

### 自动验证

```bash
./tests/run_tests.sh --verbose    # 显示详细输出
./tests/run_tests.sh --diff       # 显示预期与实际差异
```

## 添加新测试

1. 在 `tests/cases/` 创建 `.wd` 文件
2. 在 `tests/expected/` 创建对应的 `.txt` 输出文件
3. 运行测试脚本自动验证

例如：
```bash
# 创建测试
echo "int x; x := 5" > tests/cases/my_test.wd
echo "编译成功" > tests/expected/my_test.txt

# 运行并验证
./tests/run_tests.sh
```
