cmake_minimum_required(VERSION 3.10)
project(CoqProjects C)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)

# 设置编译标志
if(MSVC)
    add_compile_options(/W4)
else()
    add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# 构建 ProgrammingTask 项目
add_subdirectory(ProgrammingTask)

# 后续任务可以这样添加:
# add_subdirectory(AnotherTask)
