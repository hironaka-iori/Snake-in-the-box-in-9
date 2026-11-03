# Current replay status after milestone147

All36 pilot modules passed. Full source generation also completed:1789
modules,5089segments,263586537source bytes,within the256MiB generation cap.
The first32segments and checkpoint transfer passed in11additional modules.
The saved boundary is47accepted modules,8653deductions,195344references.
See data/pilot-completion.json and data/first-group-completion.json.
The full contradiction and actual-snake application remain pending.

Resume with ../scripts/run_full_replay.py only after checking live progress
and confirming no existing driver. Plans and accepted source bytes are
immutable. The independent source-layout audit is in
../audit/full-layout-review147.md. Large inputs and sources are available
through ../data/replay-archives.json and ../scripts/restore_archives.py.

## Original preparation record

The following describes the earlier preparation stage. Its unchecked and
deferred statuses are superseded by the accepted receipts stated above.

# Replay preparation for the unchanged 012301 certificate

The complete renamed and packed certificate passed Python RUP replay. No solver or Lean process was invoked in this preparation. The actual-snake consequence remains dependent on the parent's semantic pipeline and a future complete Lean replay.

## Inputs and scope

The source is the completed milestone145 certificate in `work/conversion-long/trimmed.lrat`, SHA256 `7e047da8e66a46d4d283a4780d84287872b275576862b9bda01713241065d932`. It has 285,541 deductions, 31,017,505 positive references, and 12,977 retained input clauses. The original full CNF has 92,656 clauses. The final derived clause has original ID 647093 and is empty.

The milestone146 variable map and compact input CNF are unchanged. The current milestone147 `LocalWindowCnf.ShareWindow146` source was independently parsed: all 102 raw chunks contain exactly the same 12,977 encoded clauses, including literal order and multiplicity. Its source SHA256 is recorded in `data/preparation-audit.json`.

## Exact transport

1. Each original retained input clause ID maps to its position, starting at 1, in `source_original_clause_ids`. Derived clause IDs retain their original values in `data/renamed.lrat.gz`.
2. The existing 5,956-variable semantic bijection is reused. All 5,323 proof-active variables remain first in that bijection. Every literal retains its sign, position and multiplicity.
3. Reusable slots are assigned using the existing last-use method. Each step reads every hint before any slot whose last use is that step is overwritten. Input slots are ordered by decreasing reference count, with original clause ID breaking ties. Freed slots are reused in increasing order.
4. The initial input slots map, in compact input order, to the first 12,977 preorder positions of a perfect binary tree. Remaining slots map bijectively to unused preorder positions. This allows the milestone146 initial-tree bridge construction to be reused with the new certificate.
5. A packed step contains its destination key, the signed literal bits plus 1, a zero delimiter, and every hint key. The implicit final zero is retained by the format's known termination convention. Packing and unpacking were compared for every step. Every hint identity was checked, including hints appearing after the first conflict.

There are 17,523 reusable slots. A tree of height 15 and 15-bit words are necessary. The literal offset remains 8192. The largest clause has 103 literals and the largest deduction has 846 references, within the existing 255-literal and 4095-reference checker limits. The final empty clause occupies tree key 11657.

`data/transport.json` records the full variable bijection, input clause order, input slots, slot-to-tree-key map, deduction destinations and last uses. `data/packed-index.jsonl.gz` records each deduction's original ID, slot, key, binary offset, literal count and reference count.

## Checks completed

- `prepare_replay.py inspect`: input hashes, exact original-to-compact core transport, every reference identity, slot plan, tree width and checker fuel bounds. Elapsed time: 12.625 seconds.
- `transport_replay.py`: complete packed RUP replay using an independent bit-mask propagation implementation, all literal and reference roundtrips, all 285,541 deductions, and the final empty clause. Elapsed time: 172.141 seconds. No compilation time is included.
- `audit_preparation.py`: current147 concrete CNF bytes, all 102 initial subtree slices, preorder transport, all 36 source hashes, copied source pins, and absence of proof placeholders or added axioms.

The complete packed replay receipt is `data/packed-replay.json`, SHA256 `00a08a185340d07eb7c4666f2e0442b4b627a8b83f02bb85baf5eec54a5405e6`. The packed binary is 71,681,134 bytes, SHA256 `e6ac5c0af7c52a11b01212c555d23287b543aabe395d3582c625263d522a05fa`.

Gzip headers record write time. The audit records uncompressed hashes for reproducible content comparison. The packed binary is deterministic.

## Lean pilot and full generation

`data/pilot-source-plan.json` lists the exact order and SHA256 of 36 prepared, unchecked Lean modules, totaling 2,279,431 bytes. Its SHA256 is `f6e57db8bd89618f9f4b3aa7ff47d5cf9e3e161ec1de4aa00b7e417db704e70f`.

The order is: fresh checker variants; generic input-tree helpers; raw-chunk extraction; 13 groups of literal subtrees; initial-tree assembly; 13 corresponding truth groups; the full original-CNF-to-initial-tree theorem; pilot data; the kernel evaluation statement; and its semantic consequence. The pilot covers the first 1,030 deductions and 6,004 references and checks the complete live-clause checkpoint after that prefix. Its final statement only transfers truth from the CNF to that checkpoint.

The generic bridge uses the completed146 method: exact subtree slices, per-chunk truth, and explicit association normalization. It introduces no unproved CNF premise beyond the ordinary assumption that all input clauses are true.

The full generation code is present in `emit_lean.py`. After the pilot passes, `python -B emit_lean.py --full --max-source-mib 256` emits the complete replay. Existing changed sources are never overwritten. The measured plan is:

| Item | Count or size |
| --- | ---: |
| Proof segments, approximately 6000 references each | 5,089 |
| Checkpoint groups, at most 32 segments each | 160 |
| Full module inventory, including the 36 pilot modules | 1,789 |
| Proof literal text | 144,362,915 bytes |
| Checkpoint literal text, conservative bound including the pilot | 115,675,881 bytes |
| Compressed checkpoint data already saved | 26,001,373 bytes |

Full literal-source emission has been deferred until the pilot is checked. This avoids allocating approximately 260 MB of Lean literals before checking the new 15-bit variant and checkpoint cost. The full generator has been inspected but has not been executed. Its 256 MiB cap may reject generation if source overhead exceeds the remaining allowance; changing that cap requires an explicit size decision, not a proof change.

The full proof is split into four-segment checking modules. Each checkpoint group has a separate composition theorem. The final intended statement is only `Unsat` for `LocalWindowCnf.ShareWindow146.cnf`. Its use for actual snakes belongs to the parent's semantic bridge.

## Remaining obligations

1. Compile the two fresh checker variants and inspect their axiom reports. The 15-bit changes affect word masks and shifts; the mathematical soundness arguments are inherited from the checked144 sources.
2. Compile all initial-tree bridge modules, then the pilot check and consequence. Record compilation limits and time independently from source preparation.
3. Generate and compile the complete 5,089-segment replay, all checkpoint transitions, group compositions and final empty-clause theorem. A passed prefix does not establish the final contradiction.
4. Combine the resulting unsatisfiability theorem with the parent's independently checked concrete clause semantics and actual-snake normalization.

The root reported that Lean 4.19 rejects its advertised `-M2048` option in this environment. Keep an external memory guard; do not use that flag. The root's fresh generic-model checks use one thread with an 8 MiB stack when required. This preparation does not change execution limits or launch jobs.

All preparation outputs are confined to this `replay` directory. Earlier milestones and parent-owned147 sources were read without modification.
