# 根目录 Makefile - 管理所有任务

.PHONY: all clean help programming-task

all: programming-task

programming-task:
	$(MAKE) -C ProgrammingTask

clean:
	$(MAKE) -C ProgrammingTask clean

help:
	@echo "可用命令:"
	@echo "  make programming-task  - 构建 ProgrammingTask 项目"
	@echo "  make clean             - 清理所有构建产物"
	@echo "  make help              - 显示此帮助信息"
	@echo ""
	@echo "ProgrammingTask 说明:"
	@echo "  cd ProgrammingTask && make help"
