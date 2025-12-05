# Root Makefile - Manages all project tasks

.PHONY: all clean help programming-task

all: programming-task

programming-task:
	$(MAKE) -C ProgrammingTask

clean:
	$(MAKE) -C ProgrammingTask clean

help:
	@echo "Available targets:"
	@echo "  make programming-task  - Build ProgrammingTask"
	@echo "  make clean             - Remove all build artifacts"
	@echo "  make help              - Show this help message"
