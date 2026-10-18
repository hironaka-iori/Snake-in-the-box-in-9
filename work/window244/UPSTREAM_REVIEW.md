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
