# 原始研究产物

[GitHub Release 分卷](https://github.com/hironaka-iori/Snake-in-the-box-in-9/releases/tag/q9-research-snapshot-2026-11-23)计划发布 870 个分卷。若 Release 页面暂不可访问，上传或校验尚未完成。下载并解包即可补齐这个研究目录中的大型证明、求解日志和原始搜索数据。源目录中识别出的 312 个编译产物未打包。源码与已纳入的可复核资料在分支中。

## 下载、校验、解包

在一个新的下载目录运行以下命令。使用该分支的 SHA256SUMS 校验分卷，再依照固定宽度的四位数分卷号还原 tar。先将变量 research_dir 设为本分支研究目录的绝对路径。

```sh
gh release download q9-research-snapshot-2026-11-23 \
  --repo hironaka-iori/Snake-in-the-box-in-9 \
  --pattern 'q9-research-2026-11-23.tar.slice-*'
shasum -a 256 -c "$research_dir/large-artifacts/SHA256SUMS"
cat q9-research-2026-11-23.tar.slice-* | tar -xf - -C "$research_dir"
```

[分卷校验和](SHA256SUMS)、[归档文件清单](archive-file-manifest.tsv)和[归档统计](archive-summary.json)记录实际捕获的路径、字节数与散列值。归档记录已有输出和运行状态，复核结论见各研究报告及对应的覆盖审计。
