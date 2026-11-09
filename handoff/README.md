# 交接：snake-in-the-box a(9)，2026-11-02

分支 `research/unconditional-241`（不要合并到 `main`）。所有进度都已在这个分支上提交；新设备只需
`git clone -b research/unconditional-241 https://github.com/hironaka-iori/Snake-in-the-box-in-9`。

## 现状

| 结果 | 状态 | 证据 |
|---|---|---|
| 191 ≤ a(9) | Lean 检查的显式 191 边 snake | `README.md` |
| a(9) ≤ 235 | **无条件，Lean 端到端检查**，只用 `propext`、`Classical.choice`、`Quot.sound` | `outputs/upper-bound-235-audit-linux.log`，`milestones/23-k6-lean/` |
| a(9) ≤ 236、237、238 | 同上（被 235 涵盖） | `outputs/upper-bound-23{6,7,8}-audit-linux.log` |
| a(9) ≤ 234 | **求解器侧已确定，Lean 链条已打通，还差构建**：792 个自动机分片和 2,815 个种子证书（其余 6,969 个键由族引理推出） | `milestones/25-k7-234/` |

235–238 的审计都只在这台云端 Linux 上、对增量构建的核心做过；还没有从源码完整重建过一次。
新设备从源码重建时会顺带补上这一点。

## 234 还差什么

最终键集 `milestones/25-k7-234/data/keys_best234.json.gz`（标签 `B234`）：11,167 个键，
λ = 6423/1544，13 位势函数，范围 8,152 / 8,191，上界 234，余量 14；全部 44,649,358 条转移已用
Python 复核。

已完成并提交：
- k7 框架（`WindowAutomaton7Defs`、`DirectionWindowBridge7`、`AggregateDirection7Conditional`）；
- B234 的数据、键、桥接、Sequence、Aggregate、复用粘合、K7 粘合模块，以及 `UpperBound234.lean`
  （把分片和新证书换成占位桩时，整条链能编译到 `upper_bound_234`）；
- H9 和 F8 两类新窗口的证书路径都已在 Lean 里走通（各抽样 5 个和 3 个），压缩编码
  （`ProofPack`、`LocalWindowCnfPack`、`LocalWindowTagsSplit`）和驱动 `gen_k7_core.py`、`replay_k7.py`。

还要算：

| 步骤 | 规模 | 估计 |
|---|---|---|
| 237/236/235 旧窗口的回放（新设备上没有，要从已提交的核心重新生成） | 1,383 个窗口 | 约 120 内核小时，约 21 GB olean |
| 2,815 个种子证书（Cnf/Sat + 回放，压缩编码，8 种子 × 5 轮证明；其余 6,969 个新键由 `LocalWindowFamilies` 的 L1/L2 引理推出） | 约 1.22 G hint | 用新检查器 `LratV3`（`replay_k7.py gen --checker v3`，约快 1.9 倍）约 45–50 CPU 小时，约 3 GB olean |
| 792 个自动机分片 | 每个 5–12 分钟、≤1.25 GB | 约 160 CPU 小时，约 0.2 GB |
| 审计 `UpperBound234`（以及 235/236/237 的完整重建审计） | | 几个小时 |

建议机器：16 核以上、64 GB 内存、约 60 GB 空闲磁盘。16 核时总共大约 1–2 天。

这台云端机器上分片只编了 18/792 个（容器反复重启，磁盘只剩约 0.4 GB），这些 olean 不值得搬，
新设备直接重编即可。

## 怎么在新设备上继续

把 `handoff/PROMPT.md` 里分隔线以下的内容整段贴给新设备上的 Claude Code。它会按顺序：装环境 →
从源码重建 237/236/235 并审计 → 构建 234 的证书和分片 → 审计 `UpperBound234` → 提交日志并报告。

## 关键文件

- `handoff/PROMPT.md`：给新设备的完整 prompt（英文）。
- `milestones/25-k7-234/README.md`：k7 自动机和 234 的求解器侧结果、降代价过程。
- `milestones/25-k7-234/lean/README.md`：234 的 Lean 链条、生成器、分片计时。
- `milestones/25-k7-234/certify/README.md`：新证书的流水线和命令（"Final key set"、"Commands for the full run"）。
- `milestones/25-k7-234/certify/PROGRESS-B234.md`：分片构建的驱动、清理和续跑方法。
- `milestones/26-replay-efficiency/README.md`：压缩编码（olean 从 9.4 降到 2.9 字节/hint）。
- `milestones/23-k6-lean/certify/README.md`：235 是怎么构建的（可作模板）。
- `milestones/10-window-aggregate/README.md`、`local-task-236-replays.md`：236/237 回放的生成方法。

## 其他研究线（结论）

- 下界：五轮搜索（局部修补、离开 bank、对称 snake、结构分析、新调色板）都没超过 191
  （`milestones/20-lower-bound-search/`、`21-snake-structure/`）。
- 局部方法的天花板：五中心约 230；六中心纯排除 235.35；k7 加 9 方向窗口能到 234，233 需要 λ ≳ 4.47
  （`milestones/11-local-ceiling/`、`22-global-arguments/`、`24-cycle-realizability/`、`27-233-probe/`，最后一个未完成）。
