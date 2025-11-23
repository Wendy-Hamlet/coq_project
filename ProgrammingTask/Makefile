# Makefile 用于构建带类型 WhileD 编译器 (ProgrammingTask)

CC = gcc
CFLAGS = -Wall -Wextra -Wpedantic -std=c99
LEX = flex
YACC = bison
YACC_FLAGS = -d

# 项目根目录和任务目录
PROJECT_ROOT ?= .
TASK_DIR = $(PROJECT_ROOT)
SRC_DIR = $(TASK_DIR)/src
INCLUDE_DIR = $(TASK_DIR)/include
BUILD_DIR = $(TASK_DIR)/build
BIN_DIR = $(BUILD_DIR)/bin
OBJ_DIR = $(BUILD_DIR)/obj

# 源文件
SOURCES = $(SRC_DIR)/main.c $(SRC_DIR)/driver.c $(SRC_DIR)/ast.c \
          $(SRC_DIR)/type.c $(SRC_DIR)/symtab.c $(SRC_DIR)/analyze.c \
          $(SRC_DIR)/ast_printer.c $(SRC_DIR)/util.c

# 生成的文件
LEX_OUT = $(BUILD_DIR)/lexer.c
YACC_OUT = $(BUILD_DIR)/parser.c
YACC_HDR = $(BUILD_DIR)/parser.h

# 对象文件
OBJECTS = $(patsubst $(SRC_DIR)/%.c,$(OBJ_DIR)/%.o,$(SOURCES)) \
          $(OBJ_DIR)/lexer.o $(OBJ_DIR)/parser.o

# 可执行文件
TARGET = $(BIN_DIR)/whiled
TOOLS = $(BIN_DIR)/ast_pretty

.PHONY: all clean directories

all: directories $(TARGET) $(TOOLS)

directories:
	@mkdir -p $(BIN_DIR) $(OBJ_DIR)

$(TARGET): $(OBJECTS)
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -o $@ $^

$(TOOLS): tools/ast_pretty.c
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -o $@ $<

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c $(YACC_HDR)
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -c -o $@ $<

$(OBJ_DIR)/lexer.o: $(LEX_OUT)
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -c -o $@ $<

$(OBJ_DIR)/parser.o: $(YACC_OUT)
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -c -o $@ $<

$(LEX_OUT): $(SRC_DIR)/lexer.l
	@mkdir -p $(BUILD_DIR)
	$(LEX) -o $@ $<

$(YACC_OUT) $(YACC_HDR): $(SRC_DIR)/parser.y
	@mkdir -p $(BUILD_DIR)
	$(YACC) $(YACC_FLAGS) -o $(YACC_OUT) $<

clean:
	rm -rf $(BUILD_DIR)

help:
	@echo "可用命令:"
	@echo "  make          - 构建项目"
	@echo "  make clean    - 删除构建产物"
	@echo "  make help     - 显示此帮助信息"
