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

上述组件阶段尚未把 Boolean `original_unsat` 接成 `RefutedParallel`。
下文的首个完整证书现已接通 case 01，其余形状仍须完成实例检查。
34 个内核反证、15,959 个计数窗口反证、覆盖与最终聚合也仍须完成；
无条件 231/230 仍未解决。

## 实际门电路子句的首个适用性检查

`ParallelShareBoolean.lean` 给出有限 Boolean 检查器及完整正确性证明。
它只在证明了窗口顶点被选中的前提下把相应位替换为真；燃料不足会拒绝。
`square_eval`、`one_eval`、`zero_eval` 将公式解释为实际空方块与两种 gate。
`checkClauses_sound` 把检查成功转成同一构造赋值满足输入 CNF 的结论。

`LocalWindowSat/ParallelShare01Gates.lean` 对已经冻结的 `ParallelShare01.raw`
直接取第 14 至 19 项（零基），在 Lean 内核中检查其全部六条子句，得到
`Snake9.LocalWindow.ParallelShare01GatePilot.gates_sound`。原模型中的子句编号
为 30712、30762、39093、39293、41163、41425；包括两个空方块子句和四个
`g1` 子句。删除首条子句中的空方块文字后，内核确认检查器拒绝。

生成器重新核对原模型的完整 CNF hash、81 条核心子句和变量映射，不以 Python
检查代替 Lean 证明。输入追溯在 `data/parallel-share-gate-pilot-inputs.json`，
增量编译与公理审计摘要在 `data/parallel-share-gate-development.json`。

```text
PYTHON milestones/28-unconditional-231-230/scripts/generate_gate_pilot.py
PYTHON milestones/28-unconditional-231-230/scripts/develop_lean.py LocalWindowSat.ParallelShare01Gates
```

这仍是六条门电路子句的适用性结论。后续须让同一变量赋值同时满足窗口/度数、
总计数器及溢出子句，才能将完整 Boolean 反证转换为 `RefutedParallel`。

## 首个完整几何证书：case 01

`ParallelShareBlocks.lean` 将计数位解释为实际几何 share 项之和的阈值；
子序列检查保留重数，保证任意所选项片段的总和不超过完整窗口 share。
`ParallelShareClauses.lean` 检查门电路、计数器合并和溢出子句；
`ParallelShareCertificate.lean` 与原有窗口/端点计数器检查器使用同一赋值，
证明 `sound` 和 `refuted_of_check`，不添加任何新的蛇几何假设。

完整实例 `LocalWindowSat/ParallelShare01.lean` 已通过 Lean：81 条核心子句
包括 8 个窗口单元、6 个度数限制、6 个空方块/gate 子句、60 个总计数器
子句和 1 个溢出单元。它核对 1073 个真实 share 项的子序列数据，并将
Boolean 反证接成 `Snake9.LocalWindow.ParallelShare01Certificate.refuted`。

`Snake9.LocalWindow.ParallelShare01Window.share_ge_21` 进一步给出：任意真实
`Snake m` 中，只要七个方向在一个单射坐标重标记下为 `[0,1,2,0,3,1,4]`，
该窗口六个内部中心的平行 share 总和至少为 21。该定理没有 certificate
假设；适用范围仍是这一个方向形状。公理只有允许的三项。

```text
PYTHON milestones/28-unconditional-231-230/scripts/generate_parallel_pilot.py
PYTHON milestones/28-unconditional-231-230/scripts/develop_lean.py LocalWindowSat.ParallelShare01Window
PYTHON milestones/28-unconditional-231-230/scripts/fresh_lean.py LocalWindowSat.ParallelShare01Window --commit COMMITTED_SOURCE
```

新鲜构建从指定 Git 提交导出全部自定义依赖，在独立目录中逐个编译；其
`LEAN_PATH` 不包含旧自定义产物目录。提交
`504a29de6a19e9accfe07bd46d1e61e9bdf2b439` 的全部 **29 个自定义模块**已重新
编译通过，耗时约 121.6 秒；最终两个目标定理仅依赖允许的三项公理。
完整源码/依赖/产物/日志 hash、编译命令、工具链与公理审计保存在
`data/parallel-share-full-pilot-fresh.json`。
**33 个其余 share 形状及完整计数窗口链尚未接通，全局 231/230 未解决。**

## 全部 34 个精确核心的适用性批次

`generate_parallel_cases.py` 将通用检查器应用到 Boolean 批次实际保留的核心。
它重新核对完整原始 CNF、核心子句索引和变量映射；为未进入核心但被端点
计数器使用的输入分配额外变量，保持原核心的所有变量编号不变。保存的
任意长度 cycle cut 使用原有无环性检查器。新增 `ParallelShareCertificateBatch`
证明逐片检查可以拼成同一赋值下的完整子句检查；每片默认含 128 条子句。

新版 case 01 的完整适用性实例已通过开发构建。case 00 含 10,988 条核心
子句、1,054 个真实 share 项、86 个检查片；数据、首尾检查片以及部分中间
检查片已通过开发构建。其完整批次结果以检查点为准，尚未宣告全部通过。

```text
PYTHON milestones/28-unconditional-231-230/scripts/applicability_batch.py prepare
PYTHON milestones/28-unconditional-231-230/scripts/applicability_batch.py run
PYTHON milestones/28-unconditional-231-230/scripts/applicability_batch.py serve --port 8797
```

批次冻结当前 Git 提交的通用自定义依赖及控制脚本，使用独立的自定义产物
目录；每个模块记录源码、依赖、产物和日志 hash，并审计最终 `sat` 和
`refuted_of_unsat`。状态、活动进程、生成输入和日志分别保存在
`runtime/applicability/state.json`、`live.json`、`cases/` 和 `logs/`。
后续核心尚未由 Boolean 批次导出时，状态为 `waiting_for_core`，不重复求解。
内存仅观测，单模块时间上限为 1800 秒；失败或超时均为未完成。

冻结闭包同时包含证书检查器与核心 CNF 导入的 `LocalWindowRename`。
首轮发现这一独立导入根遗漏，尚未到达任何模型的最终适用性定理；修复后
使用 `prepare --refresh` 保存原 manifest/state 的历史副本并重新冻结。
该操作须取得工作锁，并拒绝保留生成器已改变的模型；重新运行时逐项核对
原有检查点的源码、依赖及产物 hash，不把历史失败清除为成功。

该批次证明任意满足指定局部几何条件的蛇产生一个满足核心的赋值。
`refuted_of_unsat` 仍是带不可满足性前提的接口，须另接匹配的 Boolean
反证及任意窗口桥接；不能将两个批次的完成数直接称为最终定理的完成数。
case 01 既有的完整局部定理与 29 模块新鲜构建继续有效。

## 七方向形状覆盖与自动坐标归一化

`ParallelShareShapeBridge.lean` 已通过 Lean 检查。`coverage_checked` 在内核中
枚举七方向的所有 restricted growth strings，证明每个满足诱导路径条件的
形状都在精确的 34 项列表中。`window_shape_mem` 随即证明任意真实蛇的
七边窗口属于这张表；此结论不要求额外的覆盖假设或局部证书。

`refuted_canonical_window` 复用既有首次出现重标记及坐标置换证明，自动构造
所需坐标列表。`window_share_ge_21_of_family` 将 34 个明确的局部反证转换为
任意窗口的 share 下界；它仍保留尚待批次完成的局部反证族前提。
`LocalWindowSat/ParallelShare01CanonicalWindow.lean` 已将已完成的 case 01
接入该桥接，仅需真实蛇窗口的规范形状匹配，不再要求用户提供坐标列表。

```text
PYTHON milestones/28-unconditional-231-230/scripts/develop_lean.py LocalWindowSat.ParallelShare01CanonicalWindow
```

所有目标公理只含允许的三项。该次是源码、依赖、产物 hash 匹配的开发构建，
不是最终全局定理的新鲜构建；记录见
`data/parallel-share-shape-coverage-development.json`。形状表与 34 个冻结 CNF
记录逐项一致，未按反转合并形状。全局 231/230 仍未完成。

## 条件式 231 聚合链的源码整合

已从既有冻结提交 `75404cc705135dd1f0526ecc9f1d198d3fbf0366` 导入缺少的
45 个聚合/有限状态模块，约 14 MB 的完整闭包含 207 个自定义模块。
其余 162 个模块与本分支现有源码逐字节一致，未覆盖现有文件。
源码与依赖清单在 `data/aggregate-231-source-import.json`。
刷新远端后，贡献者分支 `4887deb02a3a51e2775ef5e81a2fb5ddc980a669`
中的条件式 231 主文件仍与该冻结版本相同；新 230 结果仍有局部前提。

`ParallelShareAggregate231.lean` 把执行用的窗口 share 之和接到该聚合定理
实际使用的 `windowShare`。219 个依赖模块已在冻结提交 `97db4f74` 的
独立目录从源码构建。最后的适配模块因一个多余的证明命令报错；提交
`27bb46d0` 删除该命令后，逐项核对 219 个依赖在新提交的源码、依赖和
产物 hash 均不变，再单独编译修复末项，公理审计通过。记录在
`data/aggregate-231-repaired-build.json`。这是独立构建基础上的末项修复
复检，不是新提交全闭包的再次新鲜构建；最终无条件定理仍须完整新鲜构建。
该链仍保留 34 个 share 反证和 15,959 个计数窗口对应的未完成前提。

## 同一证书的 FastRup 本机比较

导入贡献者提交 `4887deb02a3a51e2775ef5e81a2fb5ddc980a669` 的原始
`WinCNF`、`FastRup` 和 `FastRupCmd`。该检查器构造证明项并交给 Lean
内核检查。使用 case 00 的同一份 compact CNF 与同一份 LRAT：5,169 个
变量、10,988 条核心子句、13,291 个推导和 905,775 条提示。

旧重放的 152 个数据/检查/根模块累计约 756.27 秒；FastRup 的对应重放约
89.86 秒，加上公理审计和原核心接口转换约 112.19 秒。两次运行均存在其他
作业，且未计入共享 CNF 和通用检查器的编译；这是单份证书比较。
有效控制通过，删除冲突提示的控制被内核拒绝。两种检查器对应的核心 CNF
已由 `rfl` 直接核对，最终 `FastParallelShare00.unsat` 的公理只有允许的三项。
`Snake9.LocalWindow.unsat_of_fastRup` 还处理了两种语义对文字零的不同约定，
因而转换不需要未证明的非零文字假设。

```text
PYTHON milestones/28-unconditional-231-230/scripts/prepare_fast_rup_benchmark.py --index 0
PYTHON milestones/28-unconditional-231-230/scripts/develop_lean.py FastShare00.LocalWindowV2 --source-root milestones/28-unconditional-231-230/runtime/fast-rup/00/src
```

完整输入、源码、模块和日志 hash、公理及耗时记录在
`data/fast-rup-case00-benchmark.json`。此单例基准不能直接作为整个批次的
预计用时；完整批次状态以各自检查点为准。

## 保留检查点的 FastRup 批次切换

`scripts/fast_share_batch.py` 使用相同的原始 CNF/LRAT，从末尾空子句提取
精确依赖核心，再使用上述冻结的 FastRup 导出器。新旧提取方式在已有的
00、01、02 三份核心上产生逐字节相同的 CNF、LRAT、变量映射和 Lean
CNF。新版精简 ready 格式经现有适用性生成器读取后，case 00 的 89 个
输出文件也全部相同，记录在 `data/fast-share-core-equivalence.json`。

```text
PYTHON milestones/28-unconditional-231-230/scripts/fast_share_batch.py prepare
PYTHON milestones/28-unconditional-231-230/scripts/fast_share_batch.py handoff
PYTHON milestones/28-unconditional-231-230/scripts/fast_share_batch.py run
PYTHON milestones/28-unconditional-231-230/scripts/fast_share_batch.py serve --port 8798
```

`prepare` 校验已完成旧结果的全部源码、依赖和产物，冻结当前提交及导出器。
`handoff` 核对旧 worker 的实际命令后，停止旧重放并保留其全部已完成和
部分检查点；它不会停止独立的适用性或聚合作业。新 worker 同时持有新旧
工作锁，避免重复运行，并为每份新结果用 `rfl` 检查完整 CNF 对应关系，
审计 `unsat` 与 `original_unsat`。新状态在 `runtime/fast-kernel/`。

尚未准备的核心只生成紧凑证明及 CNF 源码，避免生成不再使用的旧重放模块。
这仍兼容适用性批次，但旧 `kernel_batch.py run` 不能直接处理这种新格式；
切换后应续跑新 worker。所有内存用量只观察，单模块超时仍记为未完成。
三项独立检查在新看板分开显示，均不等同于无条件全局上界。

case 02 的 RUP 模块通过后，完整 CNF 相等性最初触发了 Lean 内核的
`deep recursion detected`。单独提高 `maxRecDepth` 到 1,000,000 仍失败；
使用同一源码和固定 Lean 4.19.0，加 `--tstack=65536` 后约 62.88 秒通过，
`unsat` 和 `original_unsat` 的公理均只有允许的三项。记录见
`data/fast-share-stack-control.json`。此项只调整线程栈容量，没有跳过内核。
停止的批次可用 `prepare --refresh` 保存旧 manifest、状态及失败日志，
核对其余控制器、框架、导出器和生成证明未变后恢复；仍匹配的模块继续复用。

## 计数窗口的阈值、区间与已有文件

`CountWindowBridge.lean` 已通过 Lean 检查和公理审计，记录在
`data/count-window-bridge-development.json`。231 路线使用 `symK 8`：
1 至 7 是精确计数，8 代表 `[8,21]`。它不能直接套用旧的阈值 6 接口。
新的桥接证明任意阈值的完整区间解释、自动坐标归一化和窗口反转；
`coversK` 还允许 `[6,21]` 这类较宽的既有证书覆盖计数 6、7、8 三类。
`no_interval_hit` 和 `no_reverse_interval_hit` 仍明确要求对应局部反证族；
它们尚未证明 15,959 个反证或原聚合表的完整覆盖。

对冻结的 15,959 个目标逐项检查本地文件：313 份 CNF 与记录 hash 相同，
其中 202 份同时有 hash 相同的 DRUP；15,646 项未找到匹配 CNF。
另有 15 个候选文件与对应记录 hash 不符，未作为该记录的证据采纳。
这不是对这些文件数学有效性的判决。逐项清单见
`data/count-window-artifact-inventory.json`；没有把索引中的“已验证”标记
视为本机已经具备全部证明文件。

最短的四个目标是方向 `[0,1,2]` 下的计数 `(1,1)`、`(1,2)`、`(1,3)`、
`(1,4)`。`prepare_count_pairs.py` 复用现有 `D012A11`、`D012A12`、
`D012A13`、`Q012A14` 的精确 Lean CNF 和适用性源码，以固定单线程、
seed 1 配置重现缺少的 LRAT。四份新 LRAT 已独立 RUP 重放通过。
生成的 Lean 目标尚在检查，不能把这些运行准备称为四个局部定理已经完成。
其中 `(1,1)` 与 `(1,2)` 的 `refuted` 已通过 Lean 和公理审计；另外两项
仍以当前构建结果为准。

```text
PYTHON milestones/28-unconditional-231-230/scripts/prepare_count_pairs.py
PYTHON milestones/28-unconditional-231-230/scripts/develop_lean.py FastCountD012A11.LocalWindow FastCountD012A12.LocalWindow FastCountD012A13.LocalWindow FastCountQ012A14.LocalWindow --source-root milestones/28-unconditional-231-230/runtime/count-pairs/src
```

`LocalWindowSelectedClauses.unsat_of_selected` 已通过公理审计，证明反证可以
从合法选出的子句子集提升回完整几何核心。每个生成实例还须在 Lean 中
检查所选索引有效、FastRup 公式与选出的子句完全相同，才能接入原适用性
定理。原始核心及适用性源码均未改变。输入、命令、工具 hash、种子、
重放结果和生成源码清单保存在 `runtime/count-pairs/`。

`CountWindowPairs231.lean` 已检查两中心表的全部 64 个正计数组合，证明
表中禁止的组合都被上述四个区间键或其反转覆盖。任意三条连续蛇边的
规范方向均为 `[0,1,2]`，因此 `hw2_of_pairs` 将这四个局部反证准确接到
现有 231 聚合定理的 `hw2` 前提。三个目标的公理审计全部合格。
四个反证仍作为显式前提；另外两份具体反证完成前，不称为无条件 `hw2`。
`hw3` 至 `hw6` 与完整 share 族仍未消去。

本次使用独立目录复用逐项核对源码、依赖、工具、日志及产物 hash 的既有
构建，避免干扰运行中的四个反证。181 个自定义模块的有效闭包记录在
`data/count-window-pairs-development.json`，这不是最终全新鲜构建。

```text
PYTHON milestones/28-unconditional-231-230/scripts/develop_from_fresh.py CountWindowPairs231
```

## 保留已完成证明的适用性分片细化

case 00 的 `Check44` 达到原有 1800 秒上限，批次如实记为未完成。
`refine_applicability_shards.py` 在持有停止批次的锁时，将该例尚未完成的
128 子句检查细分为 16 子句检查，保留此前通过的所有模块。原 Data、CNF、
赋值、子句及目标命题均保持相同；新模块用 `take`、`drop` 分片，合并时
由 Lean 的 `rfl` 和已证明的 `checkRaw_flatMap` 检查精确拼接。

```text
PYTHON milestones/28-unconditional-231-230/scripts/refine_applicability_shards.py --case 0 --from-shard 44 --piece-size 16
PYTHON milestones/28-unconditional-231-230/scripts/applicability_batch.py run
```

修复前的状态、输入清单、失败模块日志和被替换源码保存在
`runtime/applicability/history/refine-1792607108368296200/`；脚本提交、
原清单 hash 和每个分片记录在 `data/applicability-shard-refinement.json`。
恢复后首批细分模块已经通过并写入检查点，完整适用性结果仍以批次为准。
此处没有把超时当作几何反例，也没有放宽检查器或使用不可信计算。

## 三中心计数表的完整覆盖

`CountWindowTable231.lean` 证明任意长度的正计数枚举、规范化不变性，
以及“具体表覆盖 + 对应局部反证族”蕴含任意蛇窗口满足实际禁止表条件。
`CountWindowTriples231.lean` 从冻结源集准确导出 91 个三中心区间键，
核对两种有效四边形状的全部 1,024 个正计数组合，并证明与聚合定理
完全一致的 `hw3_of_triples` 接口。上述目标已通过 Lean 和允许公理审计。
这仍要求 91 个具体反证；不能将表覆盖本身当作这些反证已完成。

```text
PYTHON milestones/28-unconditional-231-230/scripts/prepare_count_triples_table.py
PYTHON milestones/28-unconditional-231-230/scripts/develop_from_fresh.py CountWindowTriples231
```

源集提交固定为 `75404cc705135dd1f0526ecc9f1d198d3fbf0366`。输入 hash、
原始索引和输出源码 hash 在 `data/count-triples-table-input.json`；完整有效
开发闭包在 `data/count-triples-table-development.json`。本次三中心表模块
约 10.42 秒通过，属于复用已验证依赖的开发构建，不是最终全新鲜验证。
三份最短两中心反证现已通过，第四份仍在运行。

## 四至六中心覆盖的冻结检查批次

`CountWindowTablePrefix231.no_window` 已通过 Lean 和允许公理审计：任意
正计数序列都由其前两个符号及剩余后缀覆盖。183 个自定义依赖的源码、
依赖及产物 hash 已复核，记录在 `data/count-prefix-bridge-development.json`。
这证明了分片方法的完整性，尚未替代具体表检查或局部反证。

`prepare_count_higher_tables.py` 从同一冻结源集导出四中心 567 个键、
五中心 9,323 个键、六中心 5,974 个键。五、六中心各有 64 个前缀分片；
它们合起来覆盖全部正符号组合及有效方向形状。输入、原始索引和 134 个
生成文件 hash 在 `data/count-higher-table-input.json`。这些具体检查正在
运行，文件中写出的定理不能提前计为已核验结果。

```text
PYTHON milestones/28-unconditional-231-230/scripts/prepare_count_higher_tables.py
PYTHON milestones/28-unconditional-231-230/scripts/count_table_batch.py prepare
PYTHON milestones/28-unconditional-231-230/scripts/count_table_batch.py run
```

批次冻结提交 `e5e98a61f6a2088a4e9f403e9369803580f3c389`，清单、状态和
日志位于 `runtime/count-tables/`。317 个自定义模块中，184 个匹配既有
核验闭包并复用，其他模块逐项运行、保存日志并检查目标公理。它先检查
五、六中心；对独立运行中的四中心开发检查，只有源码、依赖及产物 hash
匹配时才复用，仍在运行时等待实际进程，不重复计算。内存仅观察；模块
真实超时仍作为未完成处理。看板已分别显示表覆盖与局部反证进度。

适用性 case 00 的全部分片通过后，完整列表核对遇到内核求值错误。
冻结相同源码与依赖，只增加 `--tstack=65536` 后，最终 `sat` 和
`refuted_of_unsat` 约 12.19 秒通过，公理审计合格。失败日志已存档，
逐项相等性证据在 `data/applicability-case00-stack-repair.json`。目前
适用性已完成 00、01 两个形状，新的冻结提交为
`c5edbd7c802c6592829ce4a036343693d7125fd0`。

## 第二个完整任意窗口结果

`LocalWindowSat/ParallelShare00CanonicalWindow.lean` 将已通过的 FastRup
精确核心反证与 case 00 的完整几何赋值连接。其 `canonical_refuted` 与
`share_ge_21` 均已通过 Lean 和允许公理审计：任意蛇中规范方向为
`[0,1,2,0,3,1,0]` 的七边窗口，六个中心的 share 和至少为 21。
该定理没有额外证书或局部反证前提；形状条件仍是这个单形状结果的范围。
它与原有 case 01 合计完成两个形状，不是全部 34 个形状的全局结论。

```text
PYTHON milestones/28-unconditional-231-230/scripts/assemble_share_case.py --index 0
```

432 个所需证明源文件已保存到本里程碑的 `lean/` 中；已有的 462 个模块
在源码、依赖与产物 hash 匹配后复用，新连接模块约 104.36 秒通过。
输入与完整有效开发闭包分别见 `data/share-assembly-00-input.json`、
`data/share-assembly-00-development.json`。输出使用独立的
`runtime/share-assembly/`，不改动活跃验证作业；最终仍须冻结整个全局
定理并进行不复用自定义产物的新鲜构建。

对“是否能由短窗口减少大量证书”另做了精确区间包含检查，包括反转及
同长度较宽区间。15,959 个键中有 730 个具备这种计算上的包含见证，
仍保留 15,229 个，减少约 4.6%。这些数字只描述该规则，不是数学最小值，
也不代表 730 个推论已通过 Lean。完整见证与复核脚本为
`data/count-subwindow-redundancy.json`、`scripts/audit_count_subwindows.py`。
该规则不足以明显缩小主缺口，因此继续现有证书路线。

## 资源错误后的串行恢复

三个控制任务实际遇到 Windows 1455 或 Python `MemoryError` 后退出：
Boolean 停在 `FastShare13.S34`（已完成 13/34），适用性停在 case 02
的 Data（已完成 2/34），表覆盖停在五中心 Data。后两者最后写出的
`running` 状态未能更新；已核对父子进程均不存在，保存原状态、末项
日志和全部完成记录，再将运行状态更正为等待串行恢复。记录见
`data/resource-failure-serial-recovery.json`。这些是资源错误，不是反例。

`scripts/serial_recovery.py` 核对既有两个开发任务及其 Lean 子进程的
命令和创建时间，等它们全部退出后，依次续跑四个最短计数反证、
Boolean、几何适用性、四至六中心表覆盖。它不停止现有进程、不改变
系统页面文件，也不按内存预算中止作业。每次续跑前保存检查点和末项
日志，核对控制脚本未变化；续跑使用原控制器的源码、依赖和产物
hash 检查。只有子任务退出成功且检查点达到相应完成状态才启动下一项。
实际失败则暂停队列供定时监控处理，不能把进程结束当作证明通过。

```text
PYTHON milestones/28-unconditional-231-230/scripts/serial_recovery.py --wait-pids 51960 12884 54904 50544
```

队列状态在 `runtime/serial-recovery/state.json`；PID 仅作为本次历史
记录，后续须核对实际命令和创建时间。最终无条件 231/230 仍未完成。

## 两中心连接源码已准备，等待第四个反证

`lean/CountWindowPairs231Assembly.lean` 已写出四键 `all_refuted` 和真实
聚合条件 `hw2` 的连接。它不接受额外反证族参数，但当前没有编译通过
记录，不能计为已完成定理。准备时前三个具体反证已过，仍等待
`FastCountQ012A14.LocalWindow`；记录在
`data/count-pair-assembly-preparation.json`。

第四份通过后，使用以下脚本保留四份证明的全部生成源码，逐项验证两处
供体的源码、依赖闭包与产物 hash，在独立的 `runtime/count-pair-assembly/`
目录中只编译新连接并审计公理。任何依赖缺少匹配完成记录都停止，避免
与现有任务重复构建。该脚本不会修改运行中的恢复队列或其控制器。

```text
PYTHON milestones/28-unconditional-231-230/scripts/assemble_count_pairs.py --check-ready
PYTHON milestones/28-unconditional-231-230/scripts/assemble_count_pairs.py
```

成功证据应包括 `data/count-pair-assembly-input.json` 和
`data/count-pair-assembly-development.json`，尚不能用准备记录代替。
即使此连接完成，仍须完整消去三至六中心与 share 族前提并进行最终
独立重建，才可宣称无条件全局 231。
