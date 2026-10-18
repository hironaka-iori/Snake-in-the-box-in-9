# 244 窗口路线：阶段一完成报告

**结论：无条件证明 191 ≤ a(9) ≤ 244。**
全新源码重建于 2026 年 10 月 18 日 08:48（上海时间）完成，状态为
`SUCCESS_191_244`。这不是全局最优性证明，阶段二尚无新的已证上界。

| 结论 | 证据等级 | 文件与定理 |
| --- | --- | --- |
| 紧凑 CNF 的变量及全部子句族具有必要几何解释 | Lean 已证；可执行编码审计通过 | `ENCODING.md`；`WindowClauses.lean` 及两种生成的 Geometry 模块 |
| 任意五顶点窗口归约到两种标准形状，并保持 α | Lean 已证 | `WindowNormalization.lean`：`Snake9.Window244.normalize_five_to_standard` |
| 两个局部核心无解，且实际蛇满足其全部子句 | Lean 已证 | `W223Repeated.constraints_unsat`、`W223Distinct.constraints_unsat`；对应 Geometry.constraints |
| 排除任意内部 (2,2,3) 和 (3,2,2) | Lean 已证 | `Window223Exclusion.lean`：`Snake9.no_two_two_three_internal`、`Snake9.no_three_two_two_internal` |
| 每条蛇至多 244 条边 | Lean 已证，无条件 | `UpperBound244.lean`：`Snake9.upper_bound_244` |
| 191 ≤ a(9) ≤ 244 | Lean 已证，无条件 | `UpperBound244.lean`：`Snake9.verified_interval_191_244` |
| 242 上界 | 尚未证明 | 阶段二研究目标 |

## 审计及复现

- 分支：`research/window-244`，基于 main `537513d`；阶段一代码提交依次包括
  `dcbc100`、`a9b2141`、`52305d2`、`07ca2d7`。最终文档与证据提交以该分支最新
  提交为准，避免把提交自身哈希循环写入其内容。
- 工具链 Lean 4.19.0；mathlib 固定为
  `c44e0c8ee63ca166450922a373c7409c5d26b00b`。
- 从仓库根目录执行：

```sh
python work/window244/audit_encoding.py
python work/window244/check_sequence_bounds.py
python work/spectral/verify_strengthened.py --window244 --mathlib-dir /path/to/mathlib
```

- 中断恢复：最后一条命令加 `--resume-build <原有window244构建目录>`。
- 最终清单：`outputs/window244/final-reproduction-manifest.json`。
  摘要：`final-verification.json`。最终公理日志：`FinalAudit.log`。
  全部构建日志归档：`source-build-logs.tar.gz`。
- 全新构建位于 `work/spectral/.verification/window244-i53n2a5_/`，只从源码重建
  自定义研究依赖。共 8,229 个顺序模块，9,103 个源文件哈希，4,522 项定理公理记录。
  完成后再次核对所有保存的源码、模块产物与日志哈希。
- 四个最终定理传递公理只有 `propext`、`Classical.choice`、`Quot.sound`。
  没有证明占位符、未证明自定义公理或未经内核检查的原生决策。
- 两个核心共有 4,316 条输入子句及 20,788 个 RUP 步；repeated 为
  1,588 条 / 2,327 步，distinct 为 2,728 条 / 18,461 步。
  原始 LRAT 的 3,744 / 24,895 步与裁剪后步数不同。
- 新模块观测峰值约 1,716 MiB；早期超预算模块拆分后完成核验。
- 此阶段没有新的求解器调用，复核的是已有证书。生成器和求解器均未被信任为公理。
  144/112 证据、原工作区和 main 未改动。

## 剩余义务与下一步

阶段一已无未完成证明义务。精确最优值仍未确定，191 的构造下界未提高。

值得继续窗口路线的下一步是独立复现半径三的模式普查，再通过精确序列计算
找出达到 243、242 所需的最小模式子集。仅认证必要模式，不能把 UNKNOWN 当排除。
阶段二的求解、语义桥、势函数、纯源码重建和最终审计均须单独完成。
三个已知在更大局部模型中可行的模式不应继续用半径扩张盲追。
