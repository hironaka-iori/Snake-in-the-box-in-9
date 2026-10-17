# 244 窗口路线：阶段性报告

本报告记录已保存的进展，不是阶段 1 完成声明。当前可报告的无条件区间仍为
**191 ≤ a(9) ≤ 245**。阶段 2 尚未开始。

| 结论 | 证据等级 | 文件及定理或记录 |
| --- | --- | --- |
| CNF 子句族及辅助变量具有必要的几何解释 | 编码审计；完整具体实例仍在核验 | `ENCODING.md`；`outputs/window244/encoding-audit.json` |
| 有限选中集合不能形成圈；端点至多两个 | Lean 已证（开发构建） | `WindowGeometry.lean`：`selected_no_cycle`、`endpoint_count` |
| 两类计数器的通用子句成立 | Lean 已证（开发构建） | `WindowCounters.lean`；`WindowClauses.lean` |
| 单例方块数等于合格缺失对角数 | Lean 已证（开发构建） | `WindowAlpha.lean`：`localAlpha_corner_list` |
| 坐标置换及路径反转保持 α | Lean 已证（开发构建） | `WindowPermutation.lean`：`localAlpha_permute`；`WindowReversal.lean`：`localAlpha_reverse` |
| 任意五顶点窗口覆盖两种标准形状，且保持 α | Lean 已证（开发构建） | `WindowNormalization.lean`：`normalize_five_to_standard` |
| 两份布尔公式无解 | 独立可执行证书重放通过；完整 Lean 证书检查进行中 | `encoding-audit.json`；`certificate-*-build.json` |
| 排除 (2,2,3) 后得到 244 | 条件结果 | `work/spectral/stronger/Aggregate244Conditional.lean`：`upper_244_of_no_two_two_three` |
| 无条件 244 及区间 191..244 | 尚未完成 | `Window223Exclusion.lean`、`UpperBound244.lean` 等待完整依赖及全新审计 |

上述开发证明的公理检查只出现 `propext`、`Classical.choice`、`Quot.sound`。
最终定理仍须在完整依赖上重新接受传递公理审计。

## 可复现性与保存位置

- 分支为 `research/window-244`，从 main `537513d` 建立。基础成果提交为
  `dcbc100`，通用语义桥与规范化提交为 `a9b2141`；均已推送。
- 完整命令见 `PLAN.md` 的 Reproduction 节。全新重建使用
  `python work/spectral/verify_strengthened.py --window244 --mathlib-dir <mathlib路径>`。
  中断后使用同一命令加 `--resume-build <既有重建目录>`。
- 全新重建清单：`work/spectral/.verification/window244-i53n2a5_/manifest.json`；
  各模块日志在该目录的 `logs/`。只有状态 `SUCCESS_191_244` 才表示最终链通过。
- 开发检查清单和日志：`outputs/window244/`；定格进度为
  `progress-checkpoint.json`，运行中的清单比定格报告更新。
- 旧的 144/112 证据未改动。此次未调用新的求解器；复核的是已有证书。

## 尚未完成的义务

1. 完整核验两个核心的全部 4,316 条具体子句。
2. 完整核验两份核心的全部 20,788 个 RUP 步。
3. 接通无条件排除定理和上界定理。
4. 完成全新源码重建、最终公理审计和最终文档更新。

原始 LRAT 的 3,744 / 24,895 步与裁剪后 RUP 的 2,327 / 18,461 步不同；
不能把模块数或已通过的部分当作完整证书。早期超预算模块拆分后已通过，
当前新模块由外部监控限制在约 1,800 MiB。

## 下一步判断

这条路线值得继续完成阶段 1：目前规范化、α 不变性、通用几何和计数器证明
均已可检查，剩余主要是具体实例和完整证书的核验。但这不保证最终上界已经成立。
必须等阶段 1 的完整审计通过，才评估达到 243 或 242 所需的最小模式集合。
