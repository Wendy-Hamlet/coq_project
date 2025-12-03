## analyze part testing guide
*本文档用于说明analyze.c模块测试方法*

### 测试环境以及方式
1. 在ProgrammingTask下：
```bash
make
```
经添加过相关模块的Makefile即可直接编译出可执行文件：
    build/bin/whiled.exe

2. 接着对想要分析的测试文件进行测试即可
```bash
./build/bin/whiled examples/test_{板块名}.wd
```

便会得到输出，如果无错误输出成功的语句，有误则会针对错误行数进行报错。

### 提供的简单测试样例
在examples中提供三个文件进行了不同情况的测试
1. test_ok.wd
    对于没有错误的情况进行测试。包含了基本if语句，定义与赋值语句

2. test_type_err.wd
    针对错误类型的赋值报错。

3. test_scope_err.wd
    针对未定义变量的赋值报错。


### 代码结构
include/analyze.h
src/analyze.c
examples/test_ok.wd examples/test_tyoe_err.wd examples/test_scope_err.wd