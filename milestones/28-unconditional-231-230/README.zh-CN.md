# 231 / 230 无条件化：冻结检查点

本轮目标仍是无条件的 `Snake9.upper_bound_231` 及对应区间定理。
**尚未完成，也没有声称 230 或全局最优性。**

起点为 `research/unconditional-241` 的
`9043328966d65647acba6efd62f88eceb896622d`；独立工作目录和新分支为
`research/unconditional-231-230`。远端快照见 `data/provenance.json`。
未修改其他研究者的目录，也未启动 KEEP、244 或下界搜索。

## 已核对的证据层级

| 结论 | 实际证据 | 本轮状态 |
|---|---|---|
| 191 ≤ a(9) ≤ 237 | 上游 `UpperBound237.lean` 及贡献者成功审计 | 只检查了源码与旧收据；未完成本轮独立全量重建 |
| 236 | 包装源码存在，贡献者说明证书生成仍在进行 | 不能仅凭文件存在认定已验证 |
| 六中心 231 | 条件 Lean 聚合；15,959 个精确窗口键均有 DRAT 记录；34 个 share 形状有独立检查记录 | 完整 Lean 反证及任意蛇语义桥接尚缺 |
| 七中心 230 | 89/19 密度线索；132 个 share 检查记录 | 所选 58,817 键中 55,898 个精确匹配已验证，2,919 个未匹配；有限边界常数尚须验证 |
| packing 通用工具 | 既有六个条件/恒等式定理 | 从 main 精确引入 milestone 27，保留原始来源；本轮安排源码重建 |
| 本轮九个辅助定理 | 两个新标准库 Lean 模块已实际编译 | 门电路四个结论无公理；其余只用 propext、Quot.sound；仍是辅助结论 |
| packing 缓存反例 | 精确整数检查的抽象序列 | 通过现有五中心排除与缓存限制，否定这些限制足以推出目标下界；不是实际蛇 |

贡献者 237 审计末尾仅列 `propext, Classical.choice, Quot.sound`。
新的依赖扫描发现 237 缺少 387 个生成的 `LocalWindowUnsat.Q*` 导入入口；
236 缺少 732 个 `R*` 入口。这是仓库有意不提交生成模块造成的复现缺口，
并非反驳旧定理。需按原生成器恢复并冻结完整源码后才能独立重建。

## 路线选择

优先六中心 231。它已有闭合的数值聚合，且所需 15,959 个精确键全部匹配
冻结索引。七中心批次是另一贡献者正在推进的工作，本轮不复制该批次。
packing 则仍缺全序列下界，而且保存的缓存确实容许反例。因此暂不把有限
周期上的 packing 改善翻译成所谓全局证明。

特别注意两种 share 不同：

- `SquareIncidence.shareN 12`：空方块角点按选中邻居分母分摊，带向下取整。
- `SquareIncidence.vertexShare` / `share`：平行方块按 6、3、2 分摊。

已有 `LocalWindowShareBridge` 处理前一种量，不能直接用于后一种量。

## 数值与反例

`data/arithmetic.json` 使用整数运算重现全部系数：

- 231 packing：`954v ≤ 222281 < 954·233`。
- 230 packing：`954v ≤ 221327 < 954·232`。
- 六中心：`9996m ≤ 2318820`，等价于 `1666m ≤ 386470`，故 `m ≤ 231`。
- 七中心：若 `89m ≤ 19A+C`，加上 `27(m-8) ≤ 7S` 及含两个端点的全局式，
  得 `111351m ≤ 25618707+147C`。`C ≤ 703` 足够推出 230；若 `C=693+D`，
  则需 `D ≤ 10`。本轮没有假设上游一定已证明此边界。

反例 `data/packing-counterexample.json` 取 `m=232, v=233, T=979, E=160, s0=40`，
尺度 12 的所有抽象 share 均为零，因此 `G=23496`，小于目标 `25417`，差 1921。
它满足精确关联式、端点计数下界、741 条五中心索引限制及 198 条 packing
输入记录所给限制。方向重复 `0,…,8`；顶点 0 与 18 重合，因此明确不是蛇。
这只说明抽象限制不足，不能否定几何上的 charge 下界或六中心路线。

## 依赖与复现

精确依赖表在 [DEPENDENCIES.md](DEPENDENCIES.md)，模型审计在
[ENCODING_AUDIT.md](ENCODING_AUDIT.md)。所有上游文件注明完整提交与 SHA256。
新的辅助源位于 `work/final_lean/ParallelShareTerm.lean` 和
`work/final_lean/UpperTargetArithmetic.lean`；它们不改变 `Snake9.Snake`。

从仓库根运行（Python 3.12；`PYTHON` 表示所选解释器，不是额外依赖）：

```text
PYTHON milestones/28-unconditional-231-230/scripts/audit.py
PYTHON -m pip install --target milestones/28-unconditional-231-230/runtime/packages python-sat==1.9.dev17 psutil==7.2.2
PYTHON milestones/28-unconditional-231-230/scripts/runner.py prepare --lean-bin PATH_TO_LEAN_4_19_BIN --mathlib PATH_TO_PINNED_MATHLIB --observe-memory-only
PYTHON milestones/28-unconditional-231-230/scripts/runner.py run
PYTHON milestones/28-unconditional-231-230/scripts/runner.py serve --port 8796
```

`prepare` 要求先提交源码；固定提交保存在 `runtime/manifest.json`，只从该提交
导出自定义 Lean 依赖，不复用自定义 `.olean`。mathlib 固定为
`c44e0c8ee63ca166450922a373c7409c5d26b00b`，工具链为 Lean 4.19.0。
`--timeout` 可在准备时指定。按用户后续明确要求，本轮采用 `--observe-memory-only`：
记录内存用量和峰值，不因预设内存预算或可用内存阈值中止任务。一次只运行一个任务。
省略此选项时仍可使用原来的 `--memory-mb` 预算模式。实际失败须按编译器或
求解器错误处理，不能换用不可信计算。

runner 首先重建本轮辅助组件和两类 share 的已有全局计数组件，再对 34 个
六中心 share 模型逐例核对原始 SHA256、生成 LRAT、独立执行正提示 RUP 重放。
原始证明未随上游记录提交，因而重新生成证明；模型必须与原 hash 一致。
重放器拒绝不支持的 RAT 步，不把失败或超时认作排除。
这批工作**不自动补数学证明，也不是完整 231 源码重建**。

后台状态、完整命令、日志、资源峰值、源码/依赖/产物 hash 均保存在
`runtime/manifest.json`、`runtime/state.json` 和 `build/frozen/`。
检查点在每个完成项目后原子保存；运行锁阻止重复 runner，续跑验证产物 hash。
仪表盘分别显示求解、独立重放、Lean 组件、语义证明与最终验证。
这些本机证据尚未纳入公开提交；完成后应把选定日志及最终 manifest 另行冻结提交。

## 对 230 的判断

先完成 231。230 的数值门槛合理，但不能只凭平均值 89/19 推断结果：仍需
完成具体排除集合、有限边界常数、132 个 share 证书的 Lean 与几何桥接。
本轮启动的后台批次结束后仍须人工式数学推理与 Lean 开发；不会自动产生目标定理。

## 首次受控构建与调整

冻结提交 `90dfdaaae3500e3edc6195aa92eb48b9b2ec4754` 的独立构建重新编译了
两个新辅助模块并通过九个公理审计。既有 `Snake9` 达到 679.2 MiB 时超过
按当时可用内存自动计算的 640 MiB 预算，runner 终止了自己的编译进程。
失败及产物保存在本机 `runtime/attempt-1/` 和 `build/frozen-attempt-1/`。
这不是 Lean 逻辑失败，也不是任何上界的反例；完整组件构建仍未通过。
随后独立证书阶段完成了两个模型的求解及 RUP 重放，第三项因 Windows 文件
共享冲突中断；控制器已增加原子重命名重试。用户随后明确要求不因内存预算
停止，因此恢复 `runner.py run --phase all`，取消内存中止，仅保留用量观测。
迁移前核对所有冻结源码和编码输入与新提交完全一致，控制器版本与原始输入
提交分别记录。已完成的证书仅在产物 hash 一致时续用；自定义 Lean 组件重新编译。

## 第二阶段：真正的 Lean Boolean 证书重放

取消内存中止后，第一阶段于北京时间 2026-10-21 23:40 完成：12/12 个自定义
组件从冻结源码编译，34/34 个原始模型生成 LRAT 并独立 RUP 重放。恢复后的
总耗时约 9 分 11 秒，单项最高 RSS 为 5234.1 MiB。此完成状态只对应上述批次。

新增 `ParallelShareCounter.lean` 证明完整的抽象总计数器：重复 unary 叶子、
截断合并、逐中心累积，以及总和有界时每个溢出单元成立。
`LocalWindowRename.lean` 证明把压缩变量映回原始 DIMACS 变量仍保持不可满足。
两者已实际通过 Lean 4.19.0，打印的公理仅为 `propext`、`Quot.sound`，部分
有限 Boolean 结论不依赖公理。计数器与具体 CNF 的识别和几何赋值仍须接通。

`scripts/kernel_batch.py` 继续第二阶段：从已重放证明的空子句向后取完整依赖，
保留所需原始子句；压缩变量并记录逆映射；对压缩后的 CNF/LRAT 再独立重放；
使用现有已证明 LRAT 检查器生成分片，逐片运行 `decide +kernel`。
每片保存源码、依赖闭包、编译产物 hash；每个形状最终审计 `original_unsat`。
生成数据、原始子句索引与双向追溯元数据均保存在 `runtime/kernel/`。

```text
PYTHON milestones/28-unconditional-231-230/scripts/kernel_batch.py prepare
PYTHON milestones/28-unconditional-231-230/scripts/kernel_batch.py run
PYTHON milestones/28-unconditional-231-230/scripts/kernel_batch.py serve --port 8796
```

`prepare` 要求第一阶段的 34 份匹配证书和已提交源码；使用原 manifest 的工具链。
内存只记录，不设中止阈值。单个模块时间上限为 1800 秒；超时为未完成。
本批次只证明指定 Boolean 公式不可满足，不证明这些公式覆盖任意蛇。
全局 231/230、15,959 个计数窗口的完整 Lean 反证、几何桥接和最终独立重建
仍是目标的一部分，不能用本批次完成替代。

首份试运行已通过：`Snake9.LocalWindow.ParallelShare01.original_unsat`，
只依赖 `propext`、`Classical.choice`、`Quot.sound`。该模型的核心含 81 条
输入子句、80 个变量，保留 73 条推导、180 条提示。它的全部 10 个自定义
依赖源码精确保存在 `lean/`，hash、公理及映射见 `data/kernel-pilot-01*.json`。
这证明原模型的一组明确子句不可满足；尚不证明任意蛇满足这些子句。
剩余形状已启动后台内核重放，监测使用 `runtime/kernel/state.json`。

## 平行 share 的几何桥接组件

2026-10-22 新增四个模块，均实际通过 Lean 4.19.0：

- `ParallelShareModel.lean` 定义可计算的平行 share，包含 36 个轴对、九个平移方向及精确 6/3/2 权重。
- `ParallelShareBridge.lean` 证明平移、坐标置换和路径反转不变性，并把局部 `RefutedParallel` 结论用于任意符合该规范形状的蛇窗口；share-only 情形的计数界 `[0,21]` 由既有蛇定理给出。
- `ParallelShareGeometry.lean` 从路径无环性证明平行方块最多选中三个角，再证明几何项等于 `[E,E,g1,g3,g3,g3]` 的 unary 权重。
- `ParallelShareIdentification.lean` 证明全局 `SquareIncidence.vertexShare` 与上述局部定义逐项相等，涵盖端点。

这些模块的已打印公理均在 `propext`、`Classical.choice`、`Quot.sound` 内。
验证使用有源码、依赖和产物 hash 检查的增量开发构建；不是最终全自定义闭包的新鲜构建。
开发命令为：

```text
PYTHON milestones/28-unconditional-231-230/scripts/develop_lean.py ParallelShareGeometry ParallelShareIdentification
```

本机记录在 `runtime/bridge-development/state.json`，冻结摘要在
`data/parallel-share-bridge-development.json`。复用第一阶段产物前，构建器验证其
工具链、原始闭包记录、当前源码和每个自定义依赖均匹配，并避免旧开发产物遮蔽匹配文件。

**仍缺完整 CNF 的几何满足赋值与逐子句识别**：上述组件尚未把 Boolean
`original_unsat` 接成 `RefutedParallel`。34 个内核反证、15,959 个计数窗口
反证、覆盖与最终聚合也仍须完成；无条件 231/230 仍未解决。
