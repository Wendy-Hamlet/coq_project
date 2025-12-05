# Makefile for building typed WhileD compiler (ProgrammingTask)

CC = gcc
# Add debug info for local debugging sessions
CFLAGS = -g -O0 -Wall -Wextra -Wpedantic -std=c99
LEX = flex
YACC = bison
YACC_FLAGS = -d

# Project directories
PROJECT_ROOT ?= .
TASK_DIR = $(PROJECT_ROOT)
SRC_DIR = $(TASK_DIR)/src
INCLUDE_DIR = $(TASK_DIR)/include
BUILD_DIR = $(TASK_DIR)/build
BIN_DIR = $(BUILD_DIR)/bin
OBJ_DIR = $(BUILD_DIR)/obj

# Source files
SOURCES = $(SRC_DIR)/main.c $(SRC_DIR)/driver.c $(SRC_DIR)/ast.c \
          $(SRC_DIR)/type.c $(SRC_DIR)/symtab.c $(SRC_DIR)/analyze.c \
          $(SRC_DIR)/ast_printer.c $(SRC_DIR)/util.c

# Test files
TEST_DIR = $(TASK_DIR)/tests
TEST_LEXER = $(TEST_DIR)/test_lexer.c
TEST_PARSER = $(TEST_DIR)/test_parser.c


# Generated files
LEX_OUT = $(BUILD_DIR)/lexer.c
YACC_OUT = $(BUILD_DIR)/parser.c
YACC_HDR = $(BUILD_DIR)/parser.h

# Object files
OBJECTS = $(patsubst $(SRC_DIR)/%.c,$(OBJ_DIR)/%.o,$(SOURCES)) \
          $(OBJ_DIR)/lexer.o $(OBJ_DIR)/parser.o

# Executables
TARGET = $(BIN_DIR)/whiled
TOOLS = $(BIN_DIR)/ast_pretty
TEST_LEXER_BIN = $(BIN_DIR)/test_lexer
TEST_PARSER_BIN = $(BIN_DIR)/test_parser

.PHONY: all clean directories help test

all: directories $(TARGET) $(TOOLS)

directories:
	@mkdir -p $(BIN_DIR) $(OBJ_DIR)

$(TARGET): $(OBJECTS)
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -o $@ $^

# --- 修复部分开始 ---
# 定义 ast_pretty 需要的依赖（排除 main.o, driver.o, analyze.o 以免冲突或多余）
AST_PRETTY_OBJS = $(OBJ_DIR)/ast.o $(OBJ_DIR)/type.o $(OBJ_DIR)/symtab.o \
                  $(OBJ_DIR)/util.o $(OBJ_DIR)/lexer.o $(OBJ_DIR)/parser.o \
                  $(OBJ_DIR)/ast_printer.o

# 修改规则：链接 ast_pretty.c 和它依赖的 .o 文件
$(TOOLS): tools/ast_pretty.c $(AST_PRETTY_OBJS)
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -o $@ $^
# --- 修复部分结束 ---

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c $(YACC_HDR) | directories
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -c -o $@ $<

$(OBJ_DIR)/lexer.o: $(LEX_OUT) | directories
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -c -o $@ $<

$(OBJ_DIR)/parser.o: $(YACC_OUT) | directories
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -c -o $@ $<

$(LEX_OUT): $(SRC_DIR)/lexer.l
	@mkdir -p $(BUILD_DIR)
	$(LEX) -o $@ $<

$(YACC_OUT) $(YACC_HDR): $(SRC_DIR)/parser.y
	@mkdir -p $(BUILD_DIR)
	$(YACC) $(YACC_FLAGS) -o $(YACC_OUT) $<

# Test targets
test: $(TEST_LEXER_BIN) $(TEST_PARSER_BIN)

$(TEST_LEXER_BIN): $(TEST_DIR)/test_lexer.c $(OBJ_DIR)/lexer.o $(OBJ_DIR)/parser.o $(OBJ_DIR)/util.o
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -o $@ $^

$(TEST_PARSER_BIN): $(TEST_DIR)/test_parser.c $(OBJ_DIR)/lexer.o $(OBJ_DIR)/parser.o $(OBJ_DIR)/ast.o $(OBJ_DIR)/type.o $(OBJ_DIR)/util.o
	$(CC) $(CFLAGS) -I$(INCLUDE_DIR) -I$(BUILD_DIR) -o $@ $^

clean:
	rm -rf $(BUILD_DIR)

help:
	@echo "Available targets:"
	@echo "  make            - Build main project (whiled and ast_pretty)"
	@echo "  make test       - Build unit tests (test_lexer and test_parser)"
	@echo "  make clean      - Remove all build artifacts"
	@echo "  make help       - Show this help message"
	@echo ""
	@echo "Run tests:"
	@echo "  ./build/bin/test_lexer [file.wd]"
	@echo "  ./build/bin/test_parser [file.wd]"