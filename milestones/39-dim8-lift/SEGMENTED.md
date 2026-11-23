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
* Plain-stack builds: boundary modules 3-4 s / 0.45 GB each. Piece builds: see the status section.

## Open points

* Module stack: `LratChain` must be ported (port39.py) and the chain modules converted like
  `make_cert.py`'s `modz`, so they build with `build_cert.sh` on the farm.
* Scale: a stuck cube's full LRAT may be tens of GB of text (6996…: 5 GB after 1,800 s), more than a farm
  machine's free disk. Options: binary LRAT, or a streaming pass that cuts pieces while CaDiCaL writes.
* Solve time: both whole-cube solves were still running at 30+ min; their totals decide the piece count
  (about one piece per 10 M compacted hints, ~1 h and ≤ 8 GB per piece on the measured rate).
