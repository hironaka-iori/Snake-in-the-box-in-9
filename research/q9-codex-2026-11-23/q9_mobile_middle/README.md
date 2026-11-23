# 九维中段重排搜索

取一条九维诱导路径，保留首尾两段的位置，移动中间一个至少八个顶点的连续段。对中段尝试恒等变换或交换九个轴中的任意两个，再平移到第一处接缝。第二处接缝用完整九维空间中的深度优先搜索补齐。双接缝模式在第一处还枚举一个中间顶点。过滤条件检查顶点重复、诱导弦、剩余步数及汉明距离。两段固定端各至少有五个顶点，目标为规定的边数。搜索限制包括中段的变换、剪除的窗口、接缝形式、固定端和可选的单桥节点上限。

从两种方向分别尝试；trim=1 表示先剪去该方向的最后一边，使目标与固定两端之间的奇偶性一致。同一构造可能由多个接缝位置或轴交换产生。日志中的桥搜索数是调用次数。对照输入是从有效的191边路径内部作捷径得到的189边路径。独立程序检查所有输出路径的顶点取值、互异性和每一对顶点之间的汉明距离。

用 C++20 编译器，从项目根目录运行。程序参数依次为目标边数、先剪末端的边数、每个接缝最多剪掉的原顶点数、第一处接缝取样步长、单次桥搜索节点上限、第一处是否添加中间点。

```sh
clang++ -std=c++20 -O3 q9_mobile_middle/search.cpp -o q9_mobile_middle/two_seams
python3 -B q9_mobile_middle/audit.py plant > q9_mobile_middle/planted189.words
q9_mobile_middle/two_seams 191 0 7 1 16000 1 < q9_mobile_middle/planted189.words > q9_mobile_middle/planted_double.log
q9_mobile_middle/two_seams 192 1 4 1 12000 < q9_far189_spring_20261121/comparison191.words > q9_mobile_middle/archive192.log
q9_mobile_middle/two_seams 192 1 8 1 25000 1 < q9_far189_spring_20261121/comparison191.words > q9_mobile_middle/archive_double192.log
q9_mobile_middle/two_seams 195 0 8 1 15000 < q9_degree_trade_pairs/short_run191.words > q9_mobile_middle/target195.log
q9_mobile_middle/two_seams 196 1 8 1 15000 < q9_degree_trade_pairs/short_run191.words > q9_mobile_middle/target196.log
python3 -B q9_mobile_middle/audit.py audit
```

两代新种子合并后有109类。对这些种子分为33条和其余76条，统一运行双接缝目标192、trim=1、gap=9、stride=1、每桥25,000节点，分别见 second_generation192.log、remaining192.log。rank.py 在不含本批已排除母段的77个种子中，按与131个档案类共有的最长规范连续转移词排序。对排序前12条再尝试全部168种三轴循环置换，以192、195、196为目标，gap=10。复跑时给搜索器追加两个参数 `1 cycles`，三档分别取trim=1、0、1。所有桥调用计数均可包含几何上等价或重复的构造。
