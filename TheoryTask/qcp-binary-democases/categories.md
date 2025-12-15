使用说明：

- categories.json用于给 `QCP_examples` 下的 `.c` 文件手工标注 `category`。
- 每个键是相对于 `QCP_examples` 的文件路径，值应填为分类标记（例如：`Arithmetic`、`Typical data structure`、`Typical algorithms`、`LiteOS`、`Real algorithms`等）。
- 示例条目：

  "simple_arith/add.c": "Arithmetic"

脚本行为：
- `scripts/collect_and_analyze.py` 会优先查找并读取 `categories.json`（如果存在），把对应的 `category` 写入输出统计文件 `examples_strategies_stats.json`/`examples_strategies_stats.py`。
- 如果 `categories.json` 不存在，脚本会尝试从源文件头部注释读取 `Category:`，否则退回到目录推断或 `uncategorized`。