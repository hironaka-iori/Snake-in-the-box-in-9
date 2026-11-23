# Q9 的单访 16 层全顶点 SAT 实验

目标是在 Q9 的 Q4 层序固定时寻找至少 193 个顶点的诱导路径。98 个 Q4 Hamilton 层序取自姊妹目录 `q9_q5_coupled_20261121/orders.txt`。Q9 顶点编号为 `32*layer+colour`。用于相位提示和生成固定点的 98 条实际种子逐条保存于 `seed_paths.json`。

## 模型

`layers.py` 为每个 Q9 顶点建立一个占用变量。每对相继层恰有一个共同的 Q5 颜色，其他在 Q4 中相邻的层没有共同颜色。全部占用顶点的诱导度为 2，端层分别选一个度 1 的端点。若两个接点在同一颜色，可以有单顶点中间层。选出端点路径后，对每个额外连通分量加入禁止选齐其一圈顶点的子句。完整保留一个圈会占尽该圈每个顶点的两个邻接位置，故此子句有效。

程序从原点逐分支穷举 Q5 诱导路径，通过平移覆盖所有起点。最长路径有 14 个顶点，从原点有 960 条达到此长的定向路径。每层 32 个占用位由完整等价的排序网络统计，且不超过 14 个。总数约束为 16 层亏量之和至多 224−193=31。求解使用 PySAT 的 CaDiCaL 1.9.5 接口。

## 结果与复核

- `controls0.jsonl` 和 `controls6.jsonl` 保存阳性原始数据及完整路径。相位提示不固定变量。固定试验只对每层的若干个正占用位加假设。
- `all_free.jsonl` 和 `all_free10k.jsonl` 分别在每类 500 和 10,000 次冲突预算下测试 193 点。每类独立启动求解器。
- `results4.jsonl` 测试每层固定 4 个正顶点（总共 64 个）的 98 组条件。`results4_retry.jsonl` 加深 5 个初轮未决实例，最终 98 组均获 UNSAT。`results2.jsonl` 另测 12 组每层 2 个固定点，预算 5000 次冲突，均未决。
- `cores.py` 对六组结果缩减正固定条件。最小的这份证书使用 `certificate.json` 中的 32 个顶点。层序 `010201321202123` 以外或缺少这些固定点的搜索不由此证书排除。`core.cnf`、`core.drat` 和 `drat.log` 是独立检查材料，只有这份固定条件 CNF 在此实验中执行了 DRAT 检查。
- `test_cycle.py` 用实际路径的子段加一个与路径分离的同层四环，固定整组占用位后测试懒切前 SAT、懒切后 UNSAT。`cycle_control.json` 保存该例。
- 独立几何核验程序 `audit.py` 只用 Python 标准库。它重建立方体邻接表，核对全部种子与输出阳性，以及每个相邻层对的交集、固定点和目标状态。

在本目录以带 PySAT 的 Python 执行以下命令即可复跑主要试验。路径核验可直接用系统 Python。

```sh
python -B layers.py --mode control --pins 6 --budget 3000 --max 2
python -B layers.py --mode control --pins 0 --budget 2500 --max 6
python -B layers.py --mode all --budget 10000 --pins 0
python -B layers.py --mode seeded --budget 2500 --pins 4
python -B cores.py
drat-trim core.cnf core.drat
python -B test_cycle.py
python3 -B audit.py
```
