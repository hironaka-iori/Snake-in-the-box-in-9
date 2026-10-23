# FastRup: a faster kernel-checked RUP checker (G2)

`work/spectral/stronger/FastRup.lean` (soundness: `start`, `step_sound`, `close`, standard axioms only) and `FastRupCmd.lean` (the command that builds proof terms and submits them through `addDecl`) replace the per-step `WinRup`/`WinRupImp` declarations. The final statement is unchanged, `WinCNF.unsat F`, with the same clause list `F`, so the G1 checks carry over.

Design:
- each clause is one Nat bitmask, and each hint is checked by a non-recursive step built from kernel-accelerated Nat operations;
- each mask carries a 64-bit tag in its low bits, which the kernel's number hashing uses; this halved evaluation time;
- blocks of about 25k hints form one declaration, with continuation-passing statements between blocks;
- variables are compressed to those the proof touches;
- input clauses get logarithmic-depth membership proofs.

Measured (CPU seconds, same machine and load):

| Certificate | WinRup design | FastRup | Speedup |
| --- | --- | --- | --- |
| W223Dis (17,101 steps, 926,950 hints) | 157.8 | 69.0 | 2.3x |
| Share certificate `final_a_X20` line 1 (9,594 steps, 859,813 hints) | about 334 (inputs 5.3 GB) | 93.9 (1.1 GB) | 3.6x |

Cost is about 70 µs per hint, and it scales with the hint count. CaDiCaL 2.1.3's native LRAT (`--lrat`), trimmed by `lrat_trim.py`, has 7-19% fewer hints than drat-trim `-L`. Symmetry breaking cut one 239 window from 31.5 M to 2.7 M hints. A corrupted step (one hint removed) is rejected by the kernel.

Tools: `gen_fast.py` (LRAT to Lean modules), `lrat_trim.py`, `run_w223dis.sh` (benchmark), `bench.py`.

## CRup: compact proof terms (23 October 2026)

FastRup stores about 8 application nodes per hint, which comes to 224-232 bytes per hint of `.olean`. For the 4.3e8 hints of the full 235 bridge that is about 127 GB. `CRup.lean` and `CRupCmd.lean` check a whole block in one kernel evaluation of `sl ... = true`, proved by `Eq.refl true`.
- **Database:** a list of 32-slot segments of clause masks. Each slot lookup is cached by a `Nat.rec` case split.
- **Per step:** the term stores one packed Nat of hint indices with a 48-bit tag.
- **Exports:** referenced by constant, never copied.

| Certificate | FastRup B/hint | CRup B/hint | FastRup kernel | CRup kernel |
| --- | --- | --- | --- | --- |
| W223Dis (926,950 hints) | 224 | 9.7 | 42.8 µs/hint | 51.5 µs/hint |
| u235 session `d0120341` (993,085 hints) | 232 | 11.7 | 44.6 µs/hint | 52.2 µs/hint |

The step modules use less total CPU than FastRup's (53.6 s against 58.0 s on W223Dis), with standard axioms only. A dropped hint, or a hint pointing at a slot not yet derived, is rejected by the kernel. `gen_crup.py` emits CRup modules, and `u235/gen235_crup.diff` adapts the 235 generator; the target theorems keep their type, so G1 and the window modules are unchanged.
