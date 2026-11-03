# Case 10 recovery review

The bounded audit passed for archived source bytes, reconstructed CNF, variable renaming, retained clause IDs, proof-reduction identity and generated source ports. `data/case10-audit.json` pins 474 files. No solver, Lean compiler, native RUP replay or full-graph scan was run.

## Input and reduction

Milestone 32 case 10 has seven transitions $0123042$, window vertices $[0,1,3,7,15,14,30,26]$, and six exact internal counts $(4,4,4,4,4,4)$. The proposed exclusion concerns exact counts; it does not exclude all six counts being at most four.

The ordinary and tagged radius-four encodings were reconstructed. Both complete clause lists equal the saved 67,699-clause input with 4,040 meaning variables. The recorded renaming is a bijection of all variable IDs. Applying it to the recorded original clause IDs reproduces the old 4,488-clause compact input exactly, including literal order. The active variables and every literal in the trimmed proof are bounded by 1,640.

All nine corrected gzip archives match the original files byte for byte after decompression. The corrected names include relative directory components. The preserved initial JSON confirms duplicate archive paths in the former basename-only scheme; that initial record is historical evidence, not the authoritative archive manifest.

The original proof has 69,050 deductions and 4,112,390 hints. The reduced proof has 55,823 deductions and 3,570,165 hints, using 4,239 compact-input clause IDs. Every retained deduction line is byte-identical to the original. All hints refer to earlier available clauses. The final row is the empty clause with ID 73,538, and the retained derived rows are exactly its backward dependency closure. Referenced input IDs equal the recorded retained-core list.

These checks establish reduction identity and dependency closure. They do not independently replay RUP validity. The pinned exporter records successful simulation of all packed steps, checkpoints and the final empty clause. Its source sets `simulated = true` only after those checks succeed.

## Export and proof status

The export has 202 modules, 13-bit words, literal offset 2,400, peak 6,691 slots, 590 segments and 98 checkpoints. The active-literal bound and slot count fit these parameters. All generated/isolated source pairs differ only by the intended import prefix; no selected source contains `sorry`, `admit` or `native_decide`. Emitted raw clauses, renamed meaning tree, counter metadata and clause tags were compared with the reconstructed input and mapping.

At the audit snapshot, none of these 202 modules had a successful receipt. Full Lean replay and the concrete local contradiction remain pending. A later semantic-only or placement proof must retain the refutation as an explicit premise until it is supplied.

## Graph alignment

The targeted old cycle key is $(\text{edge},d,q,c)=(3049577,304,0,27993)$. Its nine-direction word is $012341254$. Its zero-based slice $[2:9]$ is $[2,3,4,1,2,5,4]$, canonizing to $0123042$ in both orientations. Code 27,993 decodes to six fours. The six-count convention places these at centres $r+3,\ldots,r+8$, internal to the seven-transition window beginning at $r+2$; see `CountWindows.actual_symbol_slice`. Four is an exact count, unlike capped symbol six.

| Edge | Direction/history/code | Forward suffix | Forward case | Reversed case |
|---:|---|---|---:|---:|
| 1,275,804 | $(131,0,27993)$ | $0123014$ | 7 | 23 |
| 3,049,577 | $(304,0,27993)$ | $0123042$ | 10 | 10 |
| 988,624 | $(95,0,27993)$ | $0123412$ | 23 | 7 |

Cases 7 and 23 are in the same reversal orbit. Thus each of the other two old cycle edges matches both cases when reversal is allowed. The three full keys were checked against the pinned graph arrays and direction table.

The saved case-10 experiment reports 13 newly removed keys. Its replacement cycles have lengths 18 and 4. Chaining, saved weight averages and comparison arithmetic were checked:

| Profile | Mean | Range | Comparison | Integer part |
|---|---:|---:|---:|---:|
| Completed floors | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Conditional floor 18 | $496$ | $602$ | $551765/2348$ | 234 |

Neither comparison improves. The all-edge inequalities and 13-key count remain pinned producer results; this review did not recompute all graph edges. Inherited conditional restrictions also remain. These experiments establish no new upper bound for arbitrary snakes.

Remaining obligations are the concrete Lean refutation, its actual-snake transfer with the seven-transition/six-centre alignment, and its intended incorporation into the complete graph/charge argument.

## Evidence

- `data/case10-audit.json`: SHA256 `68a2fe5f86de5714395a3f79c774e0496de3151e00e25725c57a2fea2a8e5386`.
- `scripts/audit_case10.py`: SHA256 `e4d83875feb58c65f4fca19e8cb2d310f6f481ce90af5fcec5fbbb0d363d257d`.
- Reduced LRAT: SHA256 `969ac65025cf6573085ad23dfaf0384becd50bf9c6cf5b5b61d1e9335377467a`.
- Compact CNF: SHA256 `f217256e7239e47781efc2dd4093b4b61f01b1c20caa173f0b898843e6cc789a`.

The script prints its result by default; `--output` creates a new file exclusively. No original, generated or native proof file was changed.
