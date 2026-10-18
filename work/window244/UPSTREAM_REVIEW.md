# 外部 241 成果的独立复核

2026 年 10 月 18 日发现研究分支 `research/unconditional-241` 已提交无条件
241 的 Lean 定理及成功日志。为避免重复冲击 242，已保存本地阶段二检查点，
停止重复的两路核验，优先独立复核这个更强结果。原 244 证明和证据未改动。

## 固定版本与证据等级

- 固定提交：`7d418905e17fd2ea0d4666682f0019789490236a`。
- `UpperBound241.lean` 的最终定理没有局部排除前提：
  `Snake9.upper_bound_242`、`Snake9.upper_bound_241`、
  `Snake9.verified_interval_191_241`。
- 上游 `outputs/upper-bound-241-audit.log` 报告三者公理仅为
  `propext`、`Classical.choice`、`Quot.sound`。
- 已直接比较，`Snake9.lean` 与本地原始定义相同。
- **本机独立重建仍在进行中**。上游日志和定理源码尚不等于本机复核完成。
- 239 仍要求 `AllRefuted239`。上游说明 145 份内核反驳尚未完成，约有
  410 万步和 2.49 亿条提示；238 也是条件结果。本轮不扩大到其批量认证。

## 实际运行的任务

`review_upstream241.py` 从固定 Git 提交提取 `UpperBound241` 的传递源码闭包，
共 1,238 个自定义模块，在独立目录逐个重建，不导入上游或本地研究编译缓存。
仅标准工具链及固定 mathlib 使用外部依赖；Lean 为 4.19.0，mathlib 提交为
`c44e0c8ee63ca166450922a373c7409c5d26b00b`。

```sh
python work/window244/review_upstream241.py --lean-bin /path/to/lean-4.19.0/bin --mathlib-dir /path/to/mathlib
```

重新运行同一命令可从通过且哈希仍匹配的模块恢复，有文件锁防止重复启动。
每个 Lean 进程保持原来的 1,800 MiB 外部内存预算。

首轮在原始 `Snake9` 的有限示例检查处触及该预算，尚未进入新增 241
证书。首轮清单已保存为 `outputs/window244/upstream241-first-attempt.json`。
直接改为 `by decide +kernel` 仍超限。恢复版本把两个示例定理分别拆成
192 个行检查，每行用 `by decide +kernel` 检查 192 对顶点，以 `Fin.cases`
合并，并关闭此部分的异步 elaboration。定义、最终定理陈述和上游其余源码
均未改变。
清单分别保存原始 Git 源码和实际核验源码的 SHA256，并注明这一适配。
这不使用 `native_decide`，最终仍必须检查传递公理。

首个适配后的 `Snake9` 已通过（566.89 秒），`PathStructure` 和 `CubeLocal`
也通过。随后 `SquareCounterexample` 的原始 138 顶点示例同样触及预算；
该次清单已保存为 `outputs/window244/upstream241-square-first-attempt.json`。
对它采用相同的 138 行拆分，关闭异步 elaboration，其余有限检查使用
`decide +kernel`。原始和实际源码哈希继续分别记录，预算保持不变。

第二个示例模块已通过。随后 `SharedFiniteClassification` 原始模块触及预算，
其首轮清单保存在 `outputs/window244/upstream241-classification-first-attempt.json`。
恢复时仅关闭该模块的异步 elaboration，使已有的 21 行分类证明顺序处理；
证明内容和定理陈述均不变，适配及双份源码哈希已纳入清单。

顺序处理后的分类模块已通过，累计 156 个模块已核验。原始
`LocalWindowBridge` 随后触及预算，首轮清单保存在
`outputs/window244/upstream241-bridge-first-attempt.json`。恢复版本同样仅关闭
该模块的异步 elaboration，保留所有证明和定理陈述，预算不变。

桥接模块已通过，累计 167 个模块已核验。第一个证书检查模块
`LocalWindowUnsat.C223FwdDistinct.Check1` 触及预算；保存该次清单后，
将其四个既有 `ok` 定理分别放入四个子模块，原模块只导入这些子模块。
每个证明和命名空间保持原样，内核检查方式及 1,800 MiB 预算不变。
因此实际重建闭包为 1,242 个模块（比原始闭包增加四个），不代表新增证明义务。
首轮证据为 `outputs/window244/upstream241-check1-first-attempt.json`。

- 清单：`work/spectral/.verification/upstream241-7d41890/manifest.json`。
- 日志：该目录的 `logs/`；输出流在
  `outputs/window244/upstream241-review.stdout.log` 和 `.stderr.log`。
- 只有 `SUCCESS_INDEPENDENT_191_241` 及三个最终公理审计全部通过，
  才报告本机独立验证 241 完成。

此前阶段二断点：`outputs/window244/stage2/pre-upstream-review-checkpoint.json`、
`*-lean.json` 和缓存仍在。协调清单状态为
`SUPERSEDED_BY_UPSTREAM_241_REVIEW`，不是完成声明。

## 后续处理

若 241 复核通过，原阶段二争取 242 的目标已有更强成果可复用：整理来源、
复现清单和中文说明，同步论文及仓库说明，提交研究分支后停用此次自动化。
继续完整认证 239 需要新的任务范围，不因条件定理的存在而自动展开。

若遇到错误，查明具体模块和日志后修复复现方案。内存超限时应先拆分，
保留原始 Git 源码哈希并记录任何等价拆分；不可提高到超出用户预算、
削弱定理或使用未允许的决策机制来通过检查。
