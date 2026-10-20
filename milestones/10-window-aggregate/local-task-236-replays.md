# 本地任务（Mac）：236 的内核回放（r4 集合，732 个窗口）

云端 4 核机器正在做 237 的回放（2.89 亿 hint，约 11 小时），之后才轮到 236
（6.44 亿 hint，估计 25 小时）。把 236 整体放到本地跑，可以并行。

前提：`git pull --ff-only`（分支 research/unconditional-241，head ≥ 760c8c52），
Lean 4.19.0 工具链（含 `cadical`）。所有需要的核心和 Sat 模块都已提交：
`work/final_lean/LocalWindowCnf/{Q,R}*.lean`、`LocalWindowSat/{Q,R}*.lean`、
`LocalWindowDirKeysR4.lean`、`LocalWindowDirSatR4.lean`、`LocalWindowDirUnsatR4.lean`、
`milestones/10-window-aggregate/data/lean_core_direction_r4{,b}/`。

```sh
cd milestones/10-window-aggregate/scripts
# 0. 检查器（LratFast2*, LratFast2F*, LocalWindowTagsPacked）由 lake 按需构建
# 1. 生成回放（每个窗口从提交的核心重新求出 LRAT；--split 用 LratFast2，--drop-lrat 省盘；
#    可以多进程：--shard i/n，n 取核数的一半）
for i in 0 1 2 3; do
  nohup python3 run_direction_replays.py --set r4 gen --work ~/lrat-r4 --split --rounds 2 --seeds 2 \
      --drop-lrat --shard $i/4 > ~/replay-gen-r4-$i.log 2>&1 &
done
# 2. 子句可靠性（Sat）模块：单进程，内存上限 9 GB
cd ../../..
python3 work/guarded_lake_build.py LocalWindowDirSatR4 --direct --jobs 1 --heavy-jobs 1 \
    --min-free-gb 6 --rss-cap-gb 9 --trust-mtime --log work/final_lean/.lake/guarded_build_satr4.jsonl
# 3. 回放（heavy-jobs ≈ (RAM_GB - 4)/3，每个内核检查 1-3 GB；可随时中断，--trust-mtime 续跑）
cd milestones/10-window-aggregate/scripts
python3 run_direction_replays.py --set r4 build --direct --jobs 2 --heavy-jobs 6 \
    --min-free-gb 6 --rss-cap-gb 6 --trust-mtime
# 4. 合并与审计
cd ../../..
python3 work/guarded_lake_build.py LocalWindowDirUnsatR4 --direct --jobs 1 --heavy-jobs 1 \
    --min-free-gb 6 --rss-cap-gb 12 --trust-mtime
python3 work/spectral/chain_audit.py --mathlib-dir <mathlib c44e0c8e> --target UpperBound236 \
    --log outputs/upper-bound-236-audit-macos.log \
    --axioms Snake9.upper_bound_236 Snake9.verified_interval_191_236
```

注意：
- 磁盘：回放源码约 4 GB，olean 约 9 GB，LRAT 临时文件单个最大约 600 MB。
- 三个最大的窗口（`R01203A3453`、`R01203A4434`、`R01203A4443`，各 5600 万到 7500 万 hint）
  各需要约 1 个内核小时的几倍；如果本地核数多，它们排在最后不会拖慢整体。
- 如果某个 Check 模块报 `decide` 卡住（既不是 true 也不是 false），运行
  `python3 milestones/10-window-aggregate/scripts/patch_forced.py --lemmas 1500` 后续跑。
- 提交：`outputs/upper-bound-236-audit-macos.log` 和构建统计（guarded_build*.jsonl 不提交，
  把 check 模块数、内核小时、最大 RSS 贴回来）。`git pull --rebase` 后 push。
