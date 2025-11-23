# ProgrammingTask 子项目

# 包含目录
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

# 查找 flex 和 bison
find_package(FLEX)
find_package(BISON)

# 生成 lexer 和 parser
if(FLEX_FOUND)
    flex_target(Lexer ${CMAKE_CURRENT_SOURCE_DIR}/src/lexer.l ${CMAKE_CURRENT_BINARY_DIR}/lexer.c)
endif()

if(BISON_FOUND)
    bison_target(Parser ${CMAKE_CURRENT_SOURCE_DIR}/src/parser.y ${CMAKE_CURRENT_BINARY_DIR}/parser.c
                 COMPILE_FLAGS "-d")
    add_flex_bison_dependency(Lexer Parser)
endif()

# 源文件列表
set(SOURCES
    ${CMAKE_CURRENT_SOURCE_DIR}/src/main.c
    ${CMAKE_CURRENT_SOURCE_DIR}/src/driver.c
    ${CMAKE_CURRENT_SOURCE_DIR}/src/ast.c
    ${CMAKE_CURRENT_SOURCE_DIR}/src/type.c
    ${CMAKE_CURRENT_SOURCE_DIR}/src/symtab.c
    ${CMAKE_CURRENT_SOURCE_DIR}/src/analyze.c
    ${CMAKE_CURRENT_SOURCE_DIR}/src/ast_printer.c
    ${CMAKE_CURRENT_SOURCE_DIR}/src/util.c
    ${FLEX_Lexer_OUTPUTS}
    ${BISON_Parser_OUTPUTS}
)

# 主程序
add_executable(whiled ${SOURCES})

# 工具程序
add_executable(ast_pretty ${CMAKE_CURRENT_SOURCE_DIR}/tools/ast_pretty.c)

# 输出目录
set_target_properties(whiled PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
set_target_properties(ast_pretty PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
