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
