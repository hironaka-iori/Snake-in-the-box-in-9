# 从九维长路径的中段重新寻找 192 边

输入是 `q9_far189_spring_20261121/comparison189.words`、`comparison190.words`、`comparison191.words` 与 `outside189.words`。合计 4,683 个按平移、坐标置换和反向归并的长路径类别，边数为 189 至 191。

从两端合计删去 t 条边，枚举全部 t+1 种分配方式。对留下的中段，任选相邻两个转向交换顺序，相当于绕一个正方形改走另一侧。每次要求新中段的顶点不重复且无弦。中段的两个端点固定。从全部合法中段开始，搜索所有可达的这种变形，直到没有新中段，再逐一穷举其两端在整个九维立方体中的延伸。延伸时可以单独封住一端。局部结论限于这个中段族。经过带弦中间态的变形、或者根本不含上述任何中段的路径，可能产生不同结果。

| 从两端合计删去的边 | 含原始中段的正方形变形闭包规模 | 192 边见证 |
|---:|---:|---:|
| 24 | 250,346 | 完整搜索未找到 |
| 36 | 1,265,614 | 完整搜索未找到 |

原始 191 边对照、经正方形变形后得到的 190 边对照已分别逐对复查 18,336、18,145 对顶点。见 `q9_catalogue_tip_control.log` 和 `q9_catalogue_square_positive190.log`。此外保持中段不变、从两端合计去掉 42 边的 53,847 个中段也已穷举，见 `q9_catalogue_tip_trim42.log`。

复算示例（在项目目录）：

```sh
c++ -std=c++20 -O3 q9_catalogue_tip_core.cpp -o /tmp/q9-tip-core
d=q9_far189_spring_20261121
Q9_CORE_FLIP=-1 /tmp/q9-tip-core 192 36 "$d/comparison189.words" "$d/comparison190.words" "$d/comparison191.words" "$d/outside189.words"
```
