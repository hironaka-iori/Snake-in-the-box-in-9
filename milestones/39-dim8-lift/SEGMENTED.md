# Segmented (checkpoint) replay for the stuck hard cubes

## Why

Eight k = 31/32 cubes (list in `b229/README.md`) do not split: vertex and lookahead splits barely
propagate, and depth-6/7 leaves still time out (dim-8 session measurements; `b229/summary8.txt`). Their
whole-cube CaDiCaL proofs are large: 6996966996696996 had 539 M raw LRAT hints after 1,800 s,
1669966996966996 128 M after 1,200 s (raw, before core compaction). One `LocalWindowUnsat` module of
checker v3 (`lean435/tools/genv3stream.py`) cannot replay that within 12 GB, and splitting its replay into
segments does not help: a late segment that cites lemmas of many earlier segments makes the kernel decode
those segments' proof lists (`resolve` → `nthN (segP Ps m) j`), so the last segments peak like the whole
replay.

## Design (`lean/LratChain.lean`, `lean435/tools/genchain.py`)

The lemmas are cut, in proof order, into pieces of about H hints. For a cut before piece i, the boundary
B_i is the list of lemmas of pieces < i cited by some piece >= i.

* Piece i is its own module `LocalWindowChain/MOD/P<i>`. Its proof list is `Ps = B_i ++ own`, where
  `B_i` (module `B<i>`) holds the boundary lemmas as words with no hints, in segments of at most 4,000.
  The boundary segments are not checked: their truth is the piece's hypothesis
  `SegsTrue … B_i B_i.length`, lifted to `SegsTrue … Ps |B_i|` by `LratChain.segsTrue_append`. The own
  segments are checked by `LratV3.check` (`decide +kernel`) and chained by `LratV3.seg_step`.
* Piece i (not last) concludes `SegsTrue … B_{i+1} B_{i+1}.length` by `LratChain.coverChk_sound`: every
  boundary word of B_{i+1} has a reference into `Ps` (a boundary or own lemma of piece i) whose clause
  equals the word's clause. The last piece concludes `False` by `LratV3.final_false`.
* `LocalWindowUnsat/MOD` keeps genv3stream's statement `theorem unsat : Unsat cnf` and chains the pieces,
  so the rest of a certificate (`make_cert.py`'s renaming / walk modules) is unchanged.

A piece never evaluates another piece's proof data, so its kernel work and memory are those of its own
segments, its boundary and the input clauses it cites, and all pieces build in parallel once the B
modules exist. Nothing about references or boundary data is trusted: wrong data only makes a check fail.
`LratChain` uses the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Measured (test proof, k = 29 cube 0661999699966669, this machine)

* CaDiCaL 2.1.3 `--unsat`: 170 s, raw LRAT 1,585,861 lemmas / 20.4 M hints.
* Boundary sizes on the raw LRAT (`/home/user/b229/seg_stats.py`): pieces of 1 M hints: 21 pieces,
  |B| max 77,132 lemmas (452 k literals); 2 M: 11 pieces, max 77,131; 5 M: 5 pieces, max 73,618. The
  boundary stays around 5 % of the lemmas and does not grow with the number of pieces.
* After `pilot.py`: core 36,025 clauses, 21,890 vars, 468,335 lemmas, 8.92 M hints. `genchain.py
  --piece-hints 2000000`: 5 pieces, boundaries 38.6 k / 48.2 k / 45.9 k / 26.8 k lemmas, word width 16.
* Plain-stack builds: boundary modules 3-4 s / 0.45 GB each.

## Status

* Plain stack, end to end (23 Nov, this machine, one module at a time): P0 1,409 s / 6.93 GB, P1 1,270 s /
  6.85 GB, P2 1,251 s / 6.70 GB, P3 884 s / 6.24 GB, P4 501 s / 5.53 GB; top `LocalWindowUnsat` 5 s /
  0.73 GB. `#print axioms Snake9.LocalWindow.Q0661999699966669.unsat`: `[propext, Classical.choice,
  Quot.sound]`. The same proof as one genv3stream module would replay 8.92 M hints in one context; here the
  peak is 6.9 GB, set by the piece size (2 M hints) and not by the whole proof.
* Review (dim-8 session, f5553b24): no soundness flaw; the chain statement, unchecked pointers checked by
  `zipChk`, and shared raw are sound. A per-piece raw is needed only if a compacted core reaches several
  100 k clauses. Follow-up in fbfb523be: an assert that every own-lemma export chunk resolves into one segment.
* Module stack (the farm route), end to end: `prod_d8.py setup` ports and builds `LratChain`;
  `CHAIN=2000000 SOLVE_OPT=--unsat make_cert.py 116 0661999699966669 29` (same proof, 8,923,427 hints)
  then `build_cert.sh`: P0-P4 1,149 / 1,061 / 1,054 / 964 / 395 s, peaks 6.68 / 6.58 / 6.43 / 5.99 /
  5.27 GB; provenance and glue modules as for any cube. prod_d8's public check (statement read from the
  .olean alone): `Snake9.CubeProv.Q0661999699966669.unsat : Unsat (cubeCnfQ 13 116 459817509069416041 29)`
  (= 0x0661999699966669), axioms `[propext, Classical.choice, Quot.sound]`. So a chain certificate is an
  ordinary cube certificate for assembly.
* Farm route `tail_d8.py --chain H` (af7feaa77): `run --only 0661999699966669 --mem-gb 8 --procs 1 --chain
  2000000`: the whole proof (pred 9.2 GB) does not fit 8 GB, so it is regenerated as a 5-piece chain (pred
  7.0 GB per piece) and built: record `route tail-chain, chain 5, peak_mb 6681, status OK`, public check
  passed, 6,607 s in all. Disk: raw LRAT ~13 B per hint (so a 900 s solve writes ≤ ~3.5 GB), build
  directory ~0.8 GB per 9 M compacted hints.

## Open points

* Scale: a stuck cube's full LRAT may be tens of GB of text (6996…: 5 GB after 1,800 s), more than a farm
  machine's free disk. Options: binary LRAT, or a streaming pass that cuts pieces while CaDiCaL writes.
* Solve time: both whole-cube solves (6996966996696996, 1669966996966996) timed out at 7,000 s with
  1.46 B / 0.49 B raw hints and 14.4 / 5.8 GB of LRAT text. Uncapped solves without proof output of
  1669966996966996 and 1669699696699669 (k = 31) started 23 Nov 16:08 UTC on t9 (24 h cap) to get the real
  totals. These totals decide whether an LRAT run (disk, `pilot.py` memory at ~4 B per raw hint) is feasible.
