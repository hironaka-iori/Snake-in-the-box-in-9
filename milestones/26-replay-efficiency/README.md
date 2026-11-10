# Replay efficiency: `.olean` bytes and kernel time per LRAT hint

*Update, 9 November: the checker v3 (`work/final_lean/LratV3.lean`, section
[Checker v3](#checker-v3-9-november-no-clause-database-about-2x-less-kernel-time)) halves the kernel
time per hint of the packed replays.*

*Update, 10 November: Sat v2 (`work/final_lean/LocalWindowTagsW.lean`, `gen_lean_cnfsat_packed.py
--sat-v2`, section [Sat v2](#sat-v2-10-november-clause-soundness-45-6x-faster-2-3x-less-memory))
makes the clause-soundness modules 4.5-6x faster with 2-3x less memory.*

Study of 29 October 2026, about 4 h on one core (`nice -n 15`, every Lean process under a 2.9 GB
RSS guard, next to another agent's jobs on the other 3 cores). Nothing was deployed. No existing
module, `.olean` or `LocalWindowUnsat/` file was touched. Every test module was compiled with
`lean -o` into a scratch directory and deleted after measuring.

**Why.** The 234 plan (milestone 25) needs 10–34 G LRAT hints of replays. The current encoding
costs about 10 B of `.olean` per hint: the existing K build is 2,260 MB for 223 M hints. At that
rate 10 G hints need about 100 GB of disk.

## Answer

Six K windows (1.6 k to 495 k hints) were regenerated with the production pipeline
(`replay_k6.py` settings: `gen_lean_lrat.py --fast --split --noncomputable-data`, `--seg 25000
--cp 3 --group 4`, checkpoints packed with `NatPack`). They were then re-encoded and compiled. In
the tables, ms/hint is kernel CPU time divided by hints.

| lever | B/hint (`.olean`) | kernel ms/hint | peak RSS | soundness |
|---|---|---|---|---|
| **baseline** (production encoding, 6 windows) | **9.41** (8.0–10.6 on ≥ 100 k hints; 148 on a 1.6 k-hint window) | 0.176 | 0.5–1.34 GB | — |
| 1. where it goes (K012304, base) | proof literals 2.33, **list cells 3.17**, checkpoints 1.36, input slots 0.83, module headers 0.73, check/main 0.36 | — | — | — |
| 2. `--seg`/`--cp` (packed, K012304) | 25k/3: 4.95; 50k/2: 4.01; 100k/1: 3.77; 25k/1: 7.75 | 0.198; 0.197; 0.230; 0.249 | 1.32; 1.82; 2.47; 1.52 GB | none |
| 3a. proofs as packed chunks (`ProofPack`), input slots packed (`NatPack`) | 8.77 → 4.95 (K012304), 10.60 → 5.06 (K012314) | +10–15 % (0.177 → 0.198) | +0.07 GB | none (data only) |
| 3b. checkpoints length-prefixed (`ProofPack`) instead of `NatPack` | 4.95 → 4.00 | 0.205 (noise) | same | none (data only) |
| 3c. denser hint words (per-lemma width, γ, nibble, MTF) | ≤ 8 % of the hint bits (12.0–17.8 bits against 13) | not built | — | needs a new checker variant |
| 4. data inside the check module (one module per window) | 4.00 → **2.93** (K012304); 233 KB → 37 KB for a 1.6 k-hint window | 0.209 (same) | 1.38 GB (same) | none (same declarations) |
| 5. trimming | no unused hint in 1.1 M; drat-trim LRAT +35–56 % hints; 5 rounds × 8 seeds: **−15 to −17 %** hints (15–43 s of solver time per window) | proportional | — | none |
| **recommended** (3a + 3b + 4, seg 25 k, cp 3) | **2.93** over the 6 windows (2.5–3.2 at ≥ 20 k hints) | **0.211** (0.17–0.25) | 0.5–1.5 GB | none |

**Projection for 10 G hints**, about 37 k windows (all K-like, 13-bit words):

| | disk | kernel time |
|---|---|---|
| current encoding (about 10 B/hint) | about 100 GB | 0.18–0.22 ms/hint → 500–600 h |
| **recommended** | 10 G × 2.8 B + 37 k × 33 KB ≈ **29 GB** | 0.21 ms/hint ≈ **580 h** (+ about 20 h of per-window start-up) |
| recommended + 5-round proof shortening (−15 %) | **≈ 25 GB** | **≈ 500 h** |

The `LocalWindowCnf`/`Sat` modules are not replay modules, but they are now the next disk item.
They cost 0.86 MB per K-sized core (545 MB for 635 windows), so about 17 GB for the 19.5 k k6
pool keys. They store the core as a `List (List Nat)` of small literals, at about 110 B per list
cell. The same packing would bring them to about 30 KB each. This is not measured; see the end of
this README. *(Since measured: about 58 KB per K core in one packed module, see
[Production](#production).)*

## Setup

- **Windows** (`milestones/10-window-aggregate/data/lean_core_direction_k6`):
  K012031A42652 (1,580 hints), K012340A25354 (19,953), K012340A26336 (99,805),
  K012345A36344 (200,427), K012314A34355 (300,463) and K012304A43633 (495,204). All are O4k
  windows with 13-bit words, slot trees of height 11 or 12, 10–17 literals and 34–75 hints per
  lemma.
- **LRAT.** `gen_lean_core.core_lrat` (seeds 1–2, 1 round) gives exactly the hint counts recorded
  in `milestones/23-k6-lean/certify/core_lrat_hints.jsonl`, so these are the proofs of the 235
  build.
- **Compilation.** `scripts/build.py` compiles one module at a time with
  `lean -o`. It records `.olean` size, CPU seconds (`wait4`) and peak RSS.
  - **Pitfall:** `LEAN_PATH` must list the scratch output *before*
    `work/final_lean/.lake/build/lib/lean`. Otherwise an import such as
    `LocalWindowUnsat.K012304A43633.Data3` silently resolves to the production `.olean`. The first
    round of this study fell into this trap. Its kernel timings were discarded; only the runs in
    `data/runs.jsonl` are kept.
- **Noise.** The other three cores were busy. Two runs of the same check modules differed by up
  to 11 % (K012314 base: 58.5 and 65.1 s). Time differences under about 10 % are not
  significant.

## 1. Where the bytes go

A micro-benchmark (`data/offline.json`) gives the unit costs:

- a module with nothing in it costs **17.1 KB** (one entry per environment extension);
- a `List Nat` literal costs **110 B per element** for small numbers, and **about 150 B plus
  8-byte limbs** for multi-limb numbers;
- one 2,000,000-bit literal costs exactly its 250 KB.

So the per-element overhead of a list is what costs, not the bits.

K012304A43633, production encoding, 4,343,928 B for 495,204 hints (8.77 B/hint):

| component | bytes | B/hint | share |
|---|---|---|---|
| proof literals (limbs of 10,476 lemma words) | 1,153,376 | 2.33 | 27 % |
| proof list cells (10,476 × about 150 B) | about 1,571,000 | **3.17** | 36 % |
| checkpoints (6 × 64-entry `NatPack` chunks, every entry padded to the widest of its chunk) | about 675,000 | 1.36 | 16 % |
| `Data0` (3,290 input-slot keys as a literal list) | 408,640 | 0.83 | 9 % |
| 20 other data-module headers (about 18 KB each) | about 360,000 | 0.73 | 8 % |
| 5 check modules + main theorem (about 27 KB each) | 177,504 | 0.36 | 4 % |

Over the whole existing K build (2,260 MB, 13,186 files, 10.1 B/hint): the `Data0` modules are
165 MB, check and main modules 93 MB, and module headers about 240 MB. For small windows the fixed
part dominates: the 1.6 k-hint window costs 233 KB (148 B/hint), almost all of it `Data0` and
four module headers. The H9 windows of the 234 plan have a median of 1.6 k hints.

Data modules cannot be dropped once the check `.olean` exists. Lean 4.19 stores theorem values,
and `ok_k` mentions `proof_k`, so every import needs the constants. Lean 4.19 has no module
system that would strip private proofs.

## 2. Segment size and checkpoint period

All rows below are K012304A43633 with packed proofs (§3a), checkpoints in `NatPack`, and
separate modules.

| `--seg` / `--cp` / `--group` | segments | checkpoints | B/hint | kernel s | ms/hint | peak RSS |
|---|---|---|---|---|---|---|
| 25k / 3 / 4 (production) | 20 | 6 | 4.95 | 97.8 | 0.198 | 1.32 GB |
| 25k / 1 / 4 | 20 | 19 | 7.75 | 123.2 | 0.249 | 1.52 GB |
| 25k / 6 / 6 | 20 | 3 | 4.19 | 116.2 | 0.235 | 1.49 GB |
| 50k / 2 / 2 | 10 | 4 | 4.01 | 97.5 | 0.197 | 1.82 GB |
| 100k / 1 / 1 | 5 | 4 | 3.77 | 113.6 | 0.230 | 2.47 GB |
| one 100 k segment, merged (K012340A26336) | 1 | 0 | 2.30 | 22.2 | 0.222 | 2.01 GB |
| one 200–495 k segment, merged (3 windows) | — | — | — | — | — | killed at 2.9 GB |

- **Checkpoints.** A `NatPack` checkpoint costs about 107 KB at height 12. That is why rarer
  checkpoints save bytes.
- **Fewer checkpoints cost time.** Every check then replays more segments from the last
  checkpoint (cp 6). Every checkpoint adds a `build` and a `cpZ` (cp 1).
- **Segment size.** Larger segments do not lower the time per hint, and peak memory grows by
  about 0.5 GB per doubling.
- **Kernel time split** (single theorems on the production data):
  - start-up: 0.5 s;
  - loading the start database from the Cnf module (`loadRaw`): 2.4 s;
  - building a checkpoint: 1.2–2.5 s;
  - replaying 25 k hints: about 1.2 s;
  - checking them: about 3 s.

  So 25k/3 stays the best time setting. After §3b a checkpoint is 3–4× cheaper on disk, and the
  byte argument for rarer checkpoints mostly goes away.

**Recommendation:** keep `--seg 25000 --cp 3` (or 50k/2 where 1.8 GB per process is
affordable).

## 3. Denser encoding

**3a. Packed proof lists (`lean/ProofPack.lean`, `scripts/packproof.py`).**

- **Format.** A segment's proof becomes `Snake9.ProofPack.unpackL W [c₀, c₁, …]`. Each chunk
  (≤ 16 KB) is `n + 2^16·st`, and `st` holds `n` lemma words, each as `len + 2^16·x` with
  `x < 2^(W·len)`.
- **Decoder.** It is `Nat.rec` over `n` with `Nat.land`/`Nat.shiftRight`/`Nat.mul`, all
  kernel-accelerated, followed by an append by `List.rec`.
- **No proof is needed.** As with `NatPack`, `proof_k : List Nat` is only data for
  `check2`/`replay`/`cpZ`, whose theorems hold for every list. A wrong decoder could only make a
  check fail. The final `hasEmpty` and every `cpZ` compare the replayed database, so a check can
  never pass vacuously.
- **Input slots.** These are packed with the existing `NatPack` (3,290 keys: 409 KB → about
  30 KB, header included).
- **Bytes.** The proof bits stay. The 150 B per lemma goes, and the 16-bit length prefix costs
  0.04 B/hint.
- **Kernel cost.** **+10–15 %**: K012304 87.8 → 97.8 s, K012314 58.5/65.1 → 69.3 s. Chunk size
  makes no difference: 1/4/16 KB give 5.48/5.12/5.06 B/hint and 0.244/0.244/0.231 ms/hint.
- **Chunk size limit.** Keep chunks ≤ 16 KB. Lean's parser converts a hex literal in quadratic
  time: a 64 KB chunk took 17 s and a 1 MB chunk 310 s to elaborate.
- **Olean round trip.** Checked at the meta level: the 14 chunk literals of an imported `proof1`
  match the source hashes.

**3b. Checkpoints.**

- A checkpoint is the pre-order list of the 2^h tree entries. About 60 % are non-zero, at
  10–30 KB of clause words (`scripts/cpstats.py`).
- `NatPack` pads every entry to the widest of its 64-entry chunk. Clause words range from 2 to
  30 literals, so this wastes about 3×.
- Encoding the same list with `ProofPack` (length-prefixed, `0` = length 0) brings a height-12
  checkpoint from about 107 KB to about 28 KB: 4.95 → 4.00 B/hint, time unchanged.
- **Delta checkpoints** would keep 63–79 % of the entries "same as the previous checkpoint", for
  another 2–3× (`cp_delta_KB` in `data/offline.json`). They chain checkpoint evaluations,
  though, and once §3b is applied checkpoints are only 0.35 B/hint. Not pursued.

**3c. Hint words.**

- All hints are used (§5).
- Measured over the four mid-size windows (`scripts/codes.py`), per hint:

  | coding | bits |
  |---|---|
  | current fixed words | 13 |
  | width per lemma | 12.0–13.1 |
  | Elias-γ on frequency-ordered slots | 16.3–17.8 |
  | nibble varint | 13.1–14.2 |
  | 15-entry move-to-front | 12.9–13.9 |
  | order-0 entropy of the hint slots (lower bound for codings like these) | 9.6–10.2 |

- xz on the whole word stream reaches 5.4–10.1 bits per hint, against 15.3–20.4 bits per hint
  now (literals included). That redundancy is in repeated hint sequences, and a cheap kernel
  decoder cannot exploit it.
- A different hint coding needs a new checker variant. `hints2_sound` is generic in how the key
  is obtained, so the proof would carry over.
- Literal words could be sorted and delta-coded, since `lemC` builds an order-free mask. That
  saves at most about 1–2 of the 15–20 bits.
- Neither is worth a new checker against §3a, §3b and §4.

## 4. Data inside the check module

`scripts/merge.py` concatenates `Data0…n`, `Check1…g` and the main theorem of a window into one
module `LocalWindowUnsat/<W>.lean`.

- The declarations and the theorem `unsat` are the same. `#print axioms` gives `propext`,
  `Classical.choice` and `Quot.sound`.
- Kernel caches live per declaration, so the peak is that of the largest segment:

| window | hints | separate modules (§3a + §3b) | one module | kernel s | peak RSS |
|---|---|---|---|---|---|
| K012304A43633 | 495,204 | 1,979,688 B (27 modules) | **1,449,864 B** | 101.4 → 103.4 | 1.33 → 1.38 GB |
| K012031A42652 | 1,580 | (base: 233,376 B, 4 modules) | **37,040 B** | 0.8 → 1.0 | 0.51 → 0.53 GB |

- Each module saved is about 18–27 KB. For a window of 25 k hints or fewer, this is most of its
  cost.
- **Granularity.** One Lean process per window. A 10 M-hint window would be one process of about
  35 min. If finer restart points are wanted, one module per checkpoint group of about 1 M hints
  costs 20 KB each, which is negligible.
- Re-declaring the data in the check module and keeping separate data modules gains nothing:
  imports are transitive.

## 5. Trimming

- **Already minimal in the RUP sense.** Over 1.1 M hints, no hint is wasted (`scripts/lratstats.py`
  replays each lemma: every hint is unit or the final conflict). The proofs are trimmed to the
  cone of the empty clause.
- **drat-trim gives longer proofs.** Its LRAT from CaDiCaL's DRAT on the same core is longer:
  269 k against 200 k hints, and 716 k against 495 k (`scripts/dtrim.py`).
- **More core rounds and seeds** (`gen_lean_core.core_lrat(rounds=…)`, `scripts/trim.py`):

  | setting | hints | solver time per window |
  |---|---|---|
  | 3 rounds × 2 seeds | 0, −1, −2, −12 and −13 % | — |
  | **5 rounds × 8 seeds** | **−16.6 % (200 k) and −14.7 % (495 k)** | 15.5 and 42.8 s, against about 4 and 12 s |

  The k6 replays used 1 round. Any UNSAT proof of the committed core is acceptable, because the
  kernel checks every hint. This is cheaper than the replay time it saves.

## Recommended configuration

1. **Core proofs:** `core_lrat` with `rounds=5` and seeds 1–8 (the portfolio of
   `gen_lean_core.PORTFOLIO`).
2. **Generator:** `gen_lean_lrat.py --fast --split --noncomputable-data --seg 25000 --cp 3
   --force-lemmas 2000`, without the `NatPack` checkpoint pass.
3. **Post-pass:** `packproof.py <dir> W 16384`. It writes proofs and checkpoints as
   `ProofPack.unpackL`, and input slots as `NatPack.unpackL`.
4. **Merge:** `merge.py`, giving one module per window, or per group of about 1 M hints.
5. **Deployment:** this needs `ProofPack.lean` in `work/final_lean` (with a lakefile entry).
   `ProofPack.lean` has no theorems and no variants: the width `W` is an argument.

Measured on the six windows: **2.93 B/hint** in total (3,277,920 B for 1,117,432 hints, against
10,516,976 B in the base, i.e. **3.2× less**). Kernel time is **0.211 ms/hint** against 0.176,
and peak RSS 0.5–1.5 GB.

- **Fixed cost per window:** about 33 KB.
- **Variable cost:** 2.0–3.1 B/hint, hint-weighted 2.8 B/hint. O5k windows use 14-bit words, so
  add about 7 % for them.

## Production

Run of 29 October 2026 (one `lean` at a time, `nice -n 15`, 2.9 GB RSS guard, three other
jobs on the other cores). Everything was compiled with `lean -o` into a scratch directory listed
first in `LEAN_PATH` (`scripts/measure.py`) and deleted afterwards; no production `.olean` and
no `LocalWindowUnsat/` file was touched. Windows: K012031A42652 (1,580 hints), K012340A26336
(99,805) and K012304A43633 (495,204), LRAT regenerated with `core_lrat` (seeds 1–2, 1 round:
the hint counts of the 235 build). All rows are in `data/production_runs.jsonl`.

### A. Packed replays: `gen_lean_lrat.py --packed`

- **Generator.** `gen_lean_lrat.py --fast --split --noncomputable-data --packed [--pack-chunk
  16384]` writes one module `LocalWindowUnsat/<M>.lean` per window: the declarations of `Data0…n`,
  `Check1…g` and the main module, in that order, with one header. Proofs and checkpoints are
  `Snake9.ProofPack.unpackL W [...]` (§3a, §3b), input slots `Snake9.NatPack.unpackL [...]`. The
  generator checks that every packed list decodes to the list of the split layout. The O5k
  wrapper `gen_lean_lrat_o5k.py` passes the flags through. `replay_k6.py gen --packed` uses it
  and skips the `NatPack` checkpoint pass; `build` and the theorem names are unchanged.
- **Library.** `work/final_lean/ProofPack.lean` (the decoder of §3a, unchanged, no theorems) with
  a `lakefile.toml` entry.
- **Unpacked path unchanged.** Without `--packed` the 38 files written for the three windows are
  byte-identical (SHA256) to those of the previous generator, so the 235/236/237 modules are not
  affected.
- **Checks.** Each packed module compiles, and `#print axioms …unsat` gives `propext`,
  `Classical.choice`, `Quot.sound`. Also compiled: forced segments with a checkpoint
  (`--seg 400 --cp 2 --force-lemmas 20`), and the O5k self-test with `--packed`.

| window | hints | production encoding (split) | **packed (one module)** | CPU, all modules: production → packed | peak RSS |
|---|---|---|---|---|---|
| K012031A42652 | 1,580 | 232,872 B (4 modules) | **37,024 B** | 1.85 → 1.41 s | 0.51 → 0.53 GB |
| K012340A26336 | 99,805 | 828,296 B (7), 8.30 B/hint | **250,752 B, 2.51 B/hint** | 17.25 → 20.68 s (19.69 s on the packed Cnf of B) | 0.97 → 1.04 GB |
| K012304A43633 | 495,204 | 4,339,560 B (27), 8.76 B/hint | **1,449,784 B, 2.93 B/hint** | 108.87 → 108.11 s | 1.24 → 1.38 GB |
| **total** | 596,589 | 5,400,728 B, **9.05 B/hint** | 1,737,560 B, **2.91 B/hint** | **0.215 → 0.218 ms/hint** | |

The production check modules alone took 118.1 s (0.198 ms/hint). So the packed module costs
0–20 % more kernel time per window (+2 % over the three), within the noise of §Setup.

### B. Packed core and clause soundness: `gen_lean_cnfsat_packed.py`

**Where the 0.86 MB go** (K012340A26336, ablations recompiled from the production sources):

| part | `.olean` bytes |
|---|---|
| `LocalWindowCnf`: `raw`, 9,526 list cells (1,968 clauses, 7,558 literals) | **707 KB** (74 B per cell) |
| `LocalWindowCnf`: header, `window`, `bounds`, `cnf` | 24 KB |
| `LocalWindowSat`: `ctrs`, about 500 literals as list terms | **96 KB** (about 190 B per literal) |
| `LocalWindowSat`: `meaning` (`mtB`, one 19 KB literal) | 21 KB |
| `LocalWindowSat`: `tags` (`tagsOf`, one 12 KB literal) | 12 KB |
| `LocalWindowSat`: header | 21 KB |
| `LocalWindowSat`: `check`, `sat` | 6 KB |

**New decoders** (`work/final_lean/LocalWindowCnfPack.lean`, lakefile entry, no theorems;
`Tags.checkAll`, `Tags.sound`, `mtB` and `tagsOf` are untouched):

- `CnfPack.unpackL lw w`: lists of `w`-bit fields with an `lw`-bit length, in chunks
  `n + 2^16 st`. It is used for `raw` (`lw = 8`) and for the counters
  (`ctrsOf (unpackL 16 w …)`, one list `[kind, k, lits…]` each). A counter that no core clause
  uses becomes `⟨[], 2, .ends⟩`, which `ctrOK` accepts and no clause refers to.
- `CnfPack.mtS`: a sparse meaning tree in the shape of `mtB`, with one presence bit per node and
  variable-width leaves. Only the variables of the core clauses and of the kept counters get a
  meaning (K012340A26336: 1,253 of 3,232).
- `CnfPack.tagsCL`: 4 bits per tag plus its arguments, at the widths of the window.
- **Numerals.** Every decoded number is reduced to a numeral (`litCons`, `withLit`). Without
  this, each decoded literal is a new kernel term, so the kernel's per-term caches stop sharing
  work between equal entries. On K012031A42652 the check then took 22 s and 2.4 GB instead of
  18 s and 2.0 GB, and K012340A26336 went over the 2.9 GB guard.
- **Soundness by construction.** `sat` and the replay's `unsat` are both about
  `cnf = raw.map (·.map decodeLit)`, whatever `raw` decodes to, and `Tags.sound` holds for every
  meaning tree, counter list and tag list that `checkAll` accepts.

**Generator.** `gen_lean_cnfsat_packed.py --certs DIR --core DIR --out ROOT [--compare] NAME…`
writes one module `LocalWindowCnf/<M>.lean` with the usual names (`window`, `bounds`, `raw`,
`cnf`, `meaning`, `ctrs`, `tags`, `check`, `sat`).

- It repeats the checks of `gen_lean_sat.process` (encoding, CNF prefix, cycle cuts) and checks
  every encoding against a Python mirror of its decoder.
- With `--compare` it also checks that the core equals the production `raw`; this held for the
  three windows.
- Replays import `LocalWindowCnf.<M>` as before. An aggregate takes `<M>.sat` from
  `LocalWindowCnf.<M>`.
- `--split` writes the old two-module layout instead.

| core | clauses / literals | production Cnf + Sat | **packed, one module** | compile (CPU), production Cnf + Sat → packed | peak RSS |
|---|---|---|---|---|---|
| K012031A42652 | 1,009 / 3,132 | 463,720 + 155,648 = 619,368 B | **47,016 B** (13×) | 2.0 + 18.0 → 17.7 s | 2.02 → 1.99 GB |
| K012340A26336 | 1,968 / 7,558 | 731,416 + 156,392 = 887,808 B | **56,872 B** (16×) | 5.1 + 24.8 → 24.2 s | 2.54 → 2.60 GB |
| K012304A43633 | 3,290 / 13,233 | 1,006,048 + 176,552 = 1,182,600 B | **≈ 70,100 B** (17×) | Sat 29.9 s at 3.06 GB in the production log → killed at the 2.9 GB guard after 24.5 s | > 2.9 GB both |
| 51-clause stand-in (every 20th clause of K012031A42652, H9-sized) | 51 / 162 | 57,816 + 149,864 = 207,680 B | **37,496 B** (5.5×) | 0.3 + 11.2 → 10.0 s | 1.46 → 1.39 GB |

- **Large window.** K012304A43633's size is that of the module without `check`/`sat`
  (64,000 B), plus the 6,072 B those two theorems add on K012340A26336.
- **End to end.** On K012031A42652 and K012340A26336, the packed replay compiled against the
  packed Cnf module (1.28 s, 19.69 s). So did `Tags.refuted_of_sat <M>.sat <M>.unsat :
  Refuted window bounds`, and `#print axioms` gives `propext`, `Classical.choice`,
  `Quot.sound`.
- **Merging pays.** The split layout of K012031A42652 is 31,272 + 35,968 = 67,240 B, 20 KB
  more than one module.
- **Composition of the packed module** (K012340A26336, 56.9 KB):
  - literals 21 KB: `raw` 14.3, `meaning` 3.2, `tags` 3.1, `ctrs` 0.7;
  - `check` and `sat` 6 KB;
  - header and definitions about 30 KB.
- **The Sat check is the time and memory cost, and packing does not change it.**
  - Over the 635 production K modules (`guarded_build_k6.jsonl`): median 17.8 s and 2.24 GB.
    161 of them are above 2.9 GB, up to 9.1 GB.
  - Probes on K012031A42652: the 3,359 lookups `vOf meaning x` alone take 8 s and 1.2 GB. The
    same lookups on an explicit tree term take 7 s. `ctrOK` alone takes 8 s and 1.3 GB.
    Decoding `raw` takes 0.3 s.
  - So the cost is `MT.get` (structural recursion) inside `checkAll`, not the encoding.
  - Cutting it needs a checker variant with its own soundness proof: a lookup by `MT.rec`, or a
    `check` split over parts of the clause list. Both are outside this task.

### Projection for the 234 plan

Assumptions: about 37 k windows (19.5 k K-sized k6-pool cores and 17.3 k H9 cores) and 10 G
hints.

| | now | packed (A + B) |
|---|---|---|
| replays | about 100 GB (9–10 B/hint) | 10 G × 2.8 B + 37 k × 33 KB ≈ **29 GB** (≈ 25 GB with the 5-round shortening of §5) |
| Cnf + Sat | 19.5 k × 0.86 MB + 17.3 k × ≈ 0.21 MB ≈ 16.8 + 3.6 ≈ **20 GB** | 19.5 k × ≈ 58 KB + 17.3 k × ≈ 37 KB ≈ 1.1 + 0.6 ≈ **1.8 GB** |
| **total** | **≈ 120 GB** | **≈ 31 GB** |
| kernel time | replays ≈ 0.21 ms/hint ≈ 600 h; Sat ≈ 19.5 k × 21 s + 17.3 k × 10 s ≈ 160 h | the same |

- **Assumptions behind the estimates.**
  - The H9 rows use the 51-clause stand-in. Its variables (3,358) are close to the H9 CNFs (up
    to 4,513).
  - H9 cores need `alpha` padded with `None` for the uncounted last centre, in
    `gen_lean_sat.process` as well as here. That case was not run.
- **A further option, not built:** one module per window for the core, the soundness and the
  replay together. It would save about another 20 KB × 37 k ≈ 0.7 GB.

**Reproduce** (scratch root `S`, `LEAN_PATH` order as in `scripts/measure.py`):

```sh
python3 milestones/26-replay-efficiency/scripts/measure.py --src work/final_lean --out $S/olean ProofPack LocalWindowCnfPack
python3 milestones/23-k6-lean/certify/replay_k6.py gen --work $S/work --out $S/src --packed --min-disk-mb 400 d012340_a2_6-21_3_3_6-21
python3 milestones/10-window-aggregate/scripts/gen_lean_cnfsat_packed.py --certs $S/certs \
  --core milestones/10-window-aggregate/data/lean_core_direction_k6 --out $S/src --compare d012340_a2_6-21_3_3_6-21
python3 milestones/26-replay-efficiency/scripts/measure.py --src $S/src --out $S/olean --axioms \
  LocalWindowCnf.K012340A26336:Snake9.LocalWindow.K012340A26336.sat \
  LocalWindowUnsat.K012340A26336:Snake9.LocalWindow.K012340A26336.unsat
```

`gen_lean_cnfsat_packed.py` needs the CNF as `$S/certs/NAME.cnf.gz`
(`gen_k6_core.regen_cnf`). `replay_k6.py gen` writes it into `$S/work/certs` and deletes it when
it is done.

## Checker v3 (9 November): no clause database, about 2x less kernel time

Study of 9 November 2026, about 3 h on one core (`nice -n 10`, every `lean` under a 2.9 GB RSS
guard, two other agents on the other cores). Everything was compiled with `lean -o` into a scratch
directory listed first in `LEAN_PATH`; no existing checker, `.olean` or `LocalWindowUnsat/` file was
touched. The LRAT proofs are those of the 235 build (`core_lrat`, seeds 1-2, 1 round). Every row is
in `data/v3_runs.jsonl`.

**Result.** A new checker `work/final_lean/LratV3.lean` with generator `scripts/gen_lean_lrat_v3.py`
(`replay_k7.py gen --checker v3`). Same module name and same theorem `Snake9.LocalWindow.<M>.unsat :
Unsat cnf` as the packed replays, so `Tags.refuted_of_sat S.sat S.unsat` and everything downstream
are unchanged. Every `unsat` below depends on `propext`, `Classical.choice`, `Quot.sound` only.

| window | kind | hints | packed (seg 25k, cp 3): CPU, `.olean`, RSS | **v3 (seg 60k)**: CPU, `.olean`, RSS | speed-up |
|---|---|---|---|---|---|
| K012031A42652 | k6 | 1,580 | 1.35 s, 37.0 kB, 0.53 GB | 0.39 s, 36.5 kB, 0.45 GB | 3.5x |
| K012340A26336 | k6 | 99,805 | 19.31 s, 251 kB, 1.04 GB | 10.99 s, 234 kB, 1.08 GB | 1.76x |
| K012304A43633 | k6 | 495,204 | 104.42 s, 1.45 MB, 1.38 GB | 56.72 s, 1.23 MB, 1.32 GB | 1.84x |
| K012301A32534 | k6 | 1,517,293 | 390.88 s, 5.75 MB, 1.90 GB (14-bit words) | 195.89 s, 3.89 MB, 1.69 GB | **2.00x** |
| K7012031041A2555246 | H9, O5k | 2,514 | 2.27 s, 42.5 kB, 0.61 GB | 0.99 s, 41.7 kB, 0.50 GB | 2.3x |
| K701203104A6325635 | F8, O5k | 227,042 | 47.59 s, 663 kB, 1.38 GB | 28.05 s, 591 kB, 1.34 GB | 1.70x |
| **total** | | 2,343,428 | 565.8 s (0.241 ms/hint), 8.19 MB | **293.0 s (0.125 ms/hint), 6.02 MB** | **1.93x** |

CPU is the whole `lean` run (elaboration and kernel). So v3 needs about **0.12-0.13 ms per hint**
on the large windows instead of 0.21-0.26, and 2.4-2.6 B of `.olean` per hint instead of 2.9-3.8
(no checkpoints, no slot keys). For the 1.49 G hints of the 2,815 seeds of the 234 plan this is
about **50 kernel-hours instead of 92** (about 42 h with the 8 x 5 proofs), and about 1 GB less
`.olean`.

### Where the time goes in the packed checker

Measured by single-theorem probes (`decide +kernel` of parts of a check on the data of a compiled
replay module, `set_option profiler true`) on a 25 k-hint segment of K012340A26336, whose check
`ok1` takes 6.4 s:

| part | kernel s | share |
|---|---|---|
| start database `loadRaw`: 1,968 tree insertions (about 1 ms each) | 2.0 | 31 % |
| decoding the core (`rawMask` over `raw`) | 0.5 | 8 % |
| lemma tree `D` of `check2`: about 330 insertions and 1,500 lookups | 1.5 | 23 % |
| hint loop: words, flags, lemma decoding | 0.8-1.0 | 14 % |
| cached start lookups (`getS`) | 0.4 | 6 % |
| unit propagation (`hstep`) | 0.2-0.5 | 6 % |

The later checks also replay one or two earlier segments (about 0.3 s each) and rebuild the start
database from a checkpoint (`build`, 1.2-2.5 s). So more than half of the kernel time goes to the
clause tree, not to unit propagation. A sampling profile of the `lean` process (gdb, 120 stack
samples, `scripts/pmp.py`, `scripts/pmpagg.py`) agrees with that picture: the time is in generic
kernel machinery. About 20 % is in hash-table lookups of the whnf caches, 15 % in destroying those
caches at the end of each declaration, 10 % in `instantiate` (its `replace` cache), and about 20 % in
allocation and freeing. GMP work on the clause masks is under 2 %. So a step costs about the same
whatever `Nat` operation it does, and what counts is the number of kernel reduction steps.

### The checker

- **No database.** Every clause is named by where it was written:
  - an input clause by its index in `raw`;
  - a lemma by its segment and its index in that segment's proof list.
- **Hint words.** A hint word `w` of segment `c` is one of three kinds:
  - `w ≥ FLAG`: entry `w - FLAG` of the segment's reference table `t<c>`;
  - `1 ≤ w < FLAG`: lemma `w - 1` of the current segment;
  - `0`: the end of the hints.
- **References.** A reference is `idx << 12 | seg`: input clause `idx` if `seg = 0`, else lemma
  `idx` of segment `seg - 1`.
- **Tables.** A table holds the distinct references of the segment's hints into the core and into
  earlier segments (1.5-3.3 k entries per 60 k hints). It is stored as chunks of 1,024 fixed-width
  fields (`fieldT`).
- **Lemma words.** A lemma word is `n lit₁ … litₙ hint … hint 0`: a literal word is its bit
  position, and `n` is the number of literals.
- **Caching.** Every lookup goes through a `Nat.rec` on the hint word, as `LratFast2.getS` does, so
  the kernel evaluates each referenced clause once per declaration.
- **Lists.** Lists are indexed by two-level drops (`nthN`, `nthR`), written so that every
  intermediate tail is a term with literal arguments. The kernel caches those across lookups, and
  no evaluation recurses more than about 100 levels deep.
- **Segments are independent.** There is no replay and no checkpoint. `ok<c> : check OFF W M FLAG raw
  Ps t<c> c = true` mentions only the data. The last check is `andB (check …) (hasEmpty W M (segP Ps
  c))`.
- **One module serves every window.** `OFF`, `W`, `M`, `FLAG` are arguments: literals at the call
  site. The same `LratV3` serves O4k (13-bit) and O5k (14-bit) windows; the generator picks the
  narrowest word width.

**Soundness.** It is proved in `LratV3.lean` with standard axioms; the generated `unsat` was
checked with `#print axioms`.

- **Lookups.** No relation between the tables, hints and proof is needed. Whatever a word says, the
  looked-up clause is one of:
  - an input clause (`RawTrue`, from `cnfTrue` by `rawTrue_of_cnf`);
  - a lemma of an earlier segment (`SegsTrue … c`);
  - an earlier lemma of the current segment. The kernel tests `w ≤ i`; the invariant is that the
    first `i` lemmas are true;
  - the tautology `x₀ ∨ ¬x₀`, for anything out of range.

  This is `resolve_true`, `getE_true`, `getL_true`.
- **Unit propagation.** `hstep_sound` is the argument of `LratCheck`, with `OFF` as a parameter.
- **Chaining.** `seg_step : RawTrue → check … c = true → SegsTrue … c → SegsTrue … (c + 1)`, and
  `final_false` for the empty clause.
- **The tables are unchecked data, like the hints.** A wrong table can only make a check fail. A
  test with two table entries swapped made the kernel reject the module.
- **Mirror.** `gen_lean_lrat_v3.py --check` runs a Python mirror of `check`, which accepts at most
  what the kernel accepts. The generator also checks that every packed list decodes to its words.

### Ideas tried

| idea | measured | soundness | kept |
|---|---|---|---|
| **v3 database-free check, first version** (end-marked literal words, `NatPack` tables, seg 60k) | K012340 19.31 → 12.09 s, K012304 104.42 → 70.71 s, K012301 390.88 → 237.36 s (1.44-1.65x) | proved (above) | superseded by the next row |
| **+ count-prefixed literal words, tables as fixed-width chunks** (no `List.append` in the decoder) | 12.09 → 10.99, 70.71 → 56.72, 237.36 → 195.89 s (1.10-1.25x more); **1.70-2.00x in all** | proved | **yes** |
| segment size with v3 (K012304) | 30k / 60k / 125k: 57.4 / 56.7 / 59.3 s, RSS 0.98 / 1.32 / 2.03 GB; K012301 30k: 207.4 s, 1.34 GB | — | 60k default (`--seg`) |
| v3 with 25k segments, first version (K012301) | 272.5 s against 237.4 s at 60k | — | no |
| first `resolve` (segment taken from the reference by `Nat.sub`) | K012304 377.6 s (3.6x slower than packed). Every lookup into an earlier segment walked its list from the start, because the list term differed per reference | proved | fixed by the `Nat.rec` on the segment number |
| strict propagation state (`z`, `x` passed through a `Nat.rec` "let" so that they stay literals) | a 25k-hint segment 3.4 → 28-30 s | equivalent | no |
| loop variants: inline `hstep`, a dispatch function taking the word once, four hints per `Nat.rec` step, branch-free negation `z ∣ (u >>> OFF) ∣ (u <<< OFF)` with the conflict test moved to the end, two-argument lookup constants | all within ±6 % of each other (2.9-3.3 s per 25k hints; the noise of these runs is about ±10 %) | — | no |
| LRAT deletion information, a flatter or single-`Nat` database | subsumed: v3 has no database. A table holds only the clauses a segment references | — | — |
| shorter proofs (§5: 8 seeds x 5 rounds) | −15 to −18 % hints; time is proportional, so it adds to v3 | none (any proof is checked) | already in the handoff plan |

### Use

```sh
# libraries (no lakefile entry needed; as the other K7 libraries, built with --direct)
cd work/final_lean
nice -n 19 python3 ../guarded_lake_build.py --direct --trust-mtime --jobs 1 ProofPack LratV3
cd ../..
# replays with the v3 checker (default --seg 60000); everything else as in milestones/25-k7-234/certify
python3 milestones/25-k7-234/certify/replay_k7.py gen --checker v3 --work $S --plan $P ...
python3 milestones/25-k7-234/certify/replay_k7.py build
# one window by hand (LRAT and CNF in DIR, core JSON in CORE)
python3 milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py --work DIR --data CORE --out ROOT --check NAME
```

- Without `--checker v3`, `replay_k7.py` passes exactly the arguments it passed before, so the
  packed modules and their log lines are unchanged.
- The 235/236/237 modules and their checkers (`LratCheck*`, `LratFast*`, `LratFast2*`, `LratFast2F*`)
  are not touched.
- **Limits** (asserted by the generator):
  - fewer than 4,095 segments;
  - fewer than 4,094 hints per lemma (the fuel of `hints`);
  - at most `--max-lemmas` (4,000) lemmas per segment;
  - word width 13-17 bits, chosen from the largest literal bit, local index and table index.
- **Pitfall.** A scratch `LEAN_PATH` entry that contains a `LocalWindowCnf/` directory hides the
  production `LocalWindowCnf/*.olean`, even when the module wanted is not in it.

## Sat v2 (10 November): clause soundness 4.5-6x faster, 2-3x less memory

Study of 10 November 2026, about 1 h on one core (`nice -n 15`, every `lean` under the 2.9 GB guard
of `scripts/measure.py`, three other agents on the machine). Everything was compiled with `lean -o`
into a scratch directory listed first in `LEAN_PATH` and deleted afterwards. No existing checker,
decoder, `.olean` or `LocalWindowCnf/`/`LocalWindowSat/` file was touched: `Tags.checkAll`,
`Tags.sound`, `mtB`, `mtS`, `tagsOf` and the default output of the generators are unchanged
(checked byte for byte for the default, `--split` and `--part-lits` layouts). Every row is in
`data/satv2_runs.jsonl`.

**Result.** A new checker family `work/final_lean/LocalWindowTagsW.lean` (namespace `TagsW`) and the
generator option `gen_lean_cnfsat_packed.py --sat-v2` (also `gen_k7_core.py run|cnfsat --sat-v2`).
The module keeps its name and the statements of `raw`, `cnf`, `ctrs`, `tags` and `sat`, so the
replays (packed or v3) and `Tags.refuted_of_sat` are unchanged.

| core | kind | clauses / literals | production (`Tags.checkAll`): CPU, RSS, `.olean` | **`--sat-v2`**: CPU, RSS, `.olean` | speed-up |
|---|---|---|---|---|---|
| K012340A26336 | k6 | 1,968 / 7,558 | 22.75 s, 2.60 GB, 56.9 kB | **3.67 s, 0.80 GB**, 64.7 kB | **6.2x** |
| K7012031041A2555246 | H9 (`--part-lits 4000`) | 1,032 / 2,807 | 7.95 s, 1.16 GB, 50.9 kB | **1.75 s, 0.59 GB**, 62.0 kB | **4.5x** |
| K701203104A6325635 | F8 (`--part-lits 4000`) | 2,805 / 10,677 | 18.77 s, 1.41 GB, 77.0 kB | **3.98 s, 0.62 GB**, 89.1 kB | **4.7x** |
| **total** | | | 49.5 s | **9.4 s** | **5.3x** |

CPU is the whole `lean` run (imports, elaboration and kernel), the mean of 2 runs for production
and 4 (k6, H9) or 3 (F8) for v2; single runs vary by about ±15 %. At these rates the Sat/Cnf modules
of the 234 run (about 29 CPU-hours) need about 5-6 CPU-hours, and every one fits in 0.6-0.8 GB
instead of 2.0-2.6 GB, so 3-4 times as many run side by side. The `.olean` grows by 8-12 kB per
module (the flat tables), about +0.4 GB over 37 k windows.

**End to end.** On all three windows the replay `LocalWindowUnsat.<M>` compiled against the v2 module
(packed checker for K012340A26336, `LratV3` for the K7 cores: 20.3 s, 0.7 s, 27.5 s), and so did
`Tags.refuted_of_sat <M>.sat <M>.unsat : Refuted <M>.window <M>.bounds`. `#print axioms` gives
`propext`, `Classical.choice`, `Quot.sound` for every `sat` and every `refuted`.

### Where the time goes in `Tags.checkAll`

Single-theorem probes (`decide +kernel` of parts of `check` on the data of the compiled module,
`set_option profiler true`, kernel seconds; each probe pays the decoding again):

| part (K012340A26336) | production | on the flat table |
|---|---|---|
| decoding `raw`, `tags`, `ctrs` (`zip` and lengths) | 0.66 | 0.5 |
| traversal of the 7,558 core literals, no lookup (with decoding) | 1.95 | 1.95 (generic `List.all`); 0.62 with `allK` (F8 core, 10,677 literals) |
| the same with a meaning lookup per literal (1,253 distinct variables) | 7.45 | 1.37-1.84 (the lookup is free) |
| counters (`ctrOK`) | 7.4, of which ≈ 6.1 the quadratic endpoint order (`pw`); `ctrOKL`: 1.31 | 0.43 (`TagsW.ctrOK`); `ctrOKK` 0.31 on the F8 core |
| all clause checks (`ckAll`) | 12.2 | ≈ 2.5 for all of `check` with `checkAllT` (module CPU minus imports) |

- **Meaning lookups.** `MT.get` is a structural recursion on a tree of depth 12-13, and the tree is
  itself decoded lazily from `mtS`. That costs about 5 ms per distinct variable. A field of one
  numeral (`Nat.shiftRight` and `Nat.land`, GMP in the kernel) costs nothing measurable: the
  probes with and without the lookup take the same time.
- **Counters.** 6 of the 7.4 s are the all-pairs order check of the endpoint counter (286-348
  literals). `ctrOKL` (adjacent pairs) was already used by the `--part-lits` path of the H9 windows.
- **Clause comparisons.** What is left is the generic machinery: `List.contains`, `==` on lists,
  `decide (a ≤ b)`, `List.range`, equation compilers. In the kernel every such step is an
  unfolding through instances. Micro-probes on 500 vertices: `nbrs v` 1.2 ms against 0.6 ms
  written out; the neighbour count of a cut clause (`cnt` of `contains` over `nbrs`) 7 ms
  against 0.6 ms with `Nat.beq`, `List.rec` and `Bool.rec`. Per family (F8 core, generic checker
  on the flat table): a cut clause 40 ms, a `lowEnd` clause 6 ms, a `deg2` clause 2 ms.
- **Tag decoding** is under 0.3 s on every core.
- **Share core** (main's share floor 7300, `Tags.checkAllS`, in main's layout of `Structure` plus 41
  shard modules): `ctrOK` 8.5 s and `totOK` 7.9 s (`Structure`, 16.8 s and 1.79 GB), and the 41
  clause shards 59.4 s (about 0.5 s of kernel each, the rest imports).

### The checker family `TagsW`

1. **`checkAll`, `sound`** (`LocalWindowTags` with one change of representation): every definition
   takes `M : Nat → MT`, where `Tags` takes a tree read by `MT.get`. The text of the checker and
   of its soundness proof is that of `LocalWindowTags` with `M.get x` replaced by `M x`; only the
   endpoint order becomes `pwL` (adjacent entries, with `pw_of_pwL`). A certificate passes
   `getF mtab W cw iw`: field `x` of `W` bits of one numeral, with the leaf codes of `mtS`; unused
   variables are `0` (`.z`).
2. **`checkAllK`, `soundK`**: the same Bool written for the kernel: `Nat.beq`, `Nat.ble`, `Nat.blt`,
   `Nat.mod`, `Nat.div`, `List.rec`, `Bool.rec`, and the neighbour list written out (`nbrsK`).
   `checkAllK_eq : checkAllK M cs w b tags raw = checkAll M cs w b tags raw` for all arguments,
   from one equation per primitive (`allK_eq`, `memK_eq`, `sublK_eq`, `eqMapK_iff`, `cntK_eq`,
   `eraseK_eq`, `getK_eq`, `pwLK_eq`, …) and per family (`ckCutK_eq`, …, `ctrOKK_eq`).
3. **`checkAllT`, `soundT`**: literal `i` of counter `c` is read from a table (`ctrTab ctab w offs`)
   instead of by walking the decoded list (up to 348 steps per counter clause). `agreeC` checks the
   table against `ctrs` in one pass, and under it `ckAllT_eq : ckAllT = ckAllK`.

**Soundness by construction.** `sound`, `soundK`, `soundT` hold for every lookup function, counter
table, counter list and tag list that the checker accepts. So the decoders `getF` and `ctrTab`,
like `CnfPack`, need no proofs: a wrong table can only make a kernel check fail. The generator still
checks every table against a Python mirror. `sat` is `⟨TagsW.tau S E meaning ctrs, TagsW.soundT …⟩`;
`TagsW.tau` is `Tags.tau` with `M.get` replaced by `M`. Everything is proved with `propext`,
`Classical.choice`, `Quot.sound` (`#print axioms TagsW.soundT`).

### Ideas tried

| idea | measured (K012340A26336 unless noted) | soundness | kept |
|---|---|---|---|
| linear endpoint order alone (production checker, `--part-lits 100000`: `ctrOKL`, two declarations) | 22.75 → 14.18 s, 2.60 → 1.74 GB | existing (`LocalWindowTagsSplit`) | in `TagsW` |
| **flat meaning table** + linear order (`TagsW.checkAll`) | 8.83 s, 1.33 GB (2.6x); H9 3.17 s (2.5x), F8 10.25 s (1.9x) | proved (layer 1) | yes |
| **kernel-native checker** (`checkAllK`) | 3.52 s, 0.82 GB; H9 1.62 s, F8 4.31 s | proved equal (layer 2) | yes |
| **counter literals from a table**, one linear agreement pass (`checkAllT`) | 3.3-4.0 s (within noise); H9 1.56-2.1 s; F8 4.31 → 3.67-4.33 s (up to 15 %), +2-6 kB `.olean` | proved (layer 3) | yes (`--sat-v2`) |
| split into declarations (`--sat-v2 --part-lits 2000`) | 2.76 s, **0.56 GB**, but 74.6 kB `.olean` (+10 kB) | as `ckAllT_append` | option; 4000 for H9/F8 as before |
| per-clause witnesses (rule and table entries shipped with each clause) | not built: after layer 2 a clause costs about 0.3-0.5 ms of kernel time, and the remaining searches (`memK` in a 9-element list, `sublK` against `nbrsK`) cost about as much as checking a shipped position would | — | no |
| **share checker** `TagsSW` (`work/final_lean/LocalWindowTagsSW.lean`): `LocalWindowTagsShare` over two lookup functions, old families by `ckClauseK`, counters by `ctrOKK`; share families and `totOK` generic | floor 7300: `Structure` 16.82 s / 1.79 GB → 3.04-3.38 s / 0.78 GB; 41 shards 59.4 → 21.5 s; all 41 shard theorems in one module 11.6 s / 0.61 GB. **76.2 → 24.5 s (3.1x)** in main's layout | proved (`TagsSW.soundS`, standard axioms) | library only: no generator writes share Sat modules on this branch |

The share end to end: `TagsSW.checkAllS` of floor 7300 composed from the shards
(`TagsSW.ckAllS_append`, `TagsSW.checkAllS_of_parts`), its `sat`, and
`Tags.refutedShare_of_sat sat unsat : RefutedShare window bounds resolution cap` with main's replay
`LocalWindowUnsat.ShareWindow7300` (read from the `.olean` built by the floors port; not copied)
compiled with the standard axioms. The data module was converted by
`scripts/satv2_convert_share.py`. A future generator of the 490 paid share thresholds of the 233
plan (milestone 31) can use `TagsSW` the same way; a kernel-native `totOK` and share families
(as layer 2) were not written.

### Use

```sh
# library (no lakefile entry needed; like LratV3, built with --direct)
cd work/final_lean
nice -n 19 python3 ../guarded_lake_build.py --direct --trust-mtime --jobs 1 LocalWindowTagsW
cd ../..
# k6 cores
python3 milestones/10-window-aggregate/scripts/gen_lean_cnfsat_packed.py --certs $S/certs \
  --core milestones/10-window-aggregate/data/lean_core_direction_k6 --out $S/src --sat-v2 NAME
# k7 cores (H9, F8; --part-lits 4000 is the default there)
python3 milestones/25-k7-234/certify/gen_k7_core.py cnfsat --work $S/work --out $S/src --sat-v2 NAME
python3 milestones/25-k7-234/certify/gen_k7_core.py run ... --sat-v2
```

- `LocalWindowCnfPack` is still needed (it decodes `raw`, `ctrs`, `tags`); `LocalWindowTagsSplit` is
  not imported by `--sat-v2` modules.
- Use one checker per module; v2 and production modules can be mixed freely in one chain, since
  every `sat` has the same statement.
- The `.olean` of a `--sat-v2` module is 8-12 kB larger. `LocalWindowTagsW.olean` itself is a new
  library dependency of every such module.

## What this does not cover

- **Cnf/Sat modules.** *(Done since, see [Production](#production).)* These are not studied here. `raw` is a literal `List (List Nat)`: the
  1,968 clauses and 7,558 literals of K012340A26336 cost 731 KB. A packed `raw` (about 12 KB of
  bits) is plausible, but the Sat proofs and `loadRaw` consume `raw`, and whether they still
  elaborate and how fast has not been tested. H9 cores are tiny (9–57 clauses in the samples of
  milestone 25), so this concerns the about 19.5 k k6-pool keys.
- **The decode overhead of §3a.** It was not optimised. Possible remedies, untested: fewer kernel
  steps per lemma (a single recursion instead of `app`), or packing only checkpoints and slots
  (§3b + §4 without §3a, which would give about 6 B/hint at the base speed).
- **Wider trees.** Only O4k windows with trees of height 11 and 12 were measured. Height 13
  doubles the checkpoint entries.

## Files

| path | contents |
|---|---|
| `lean/ProofPack.lean` | the chunk decoder (no theorems) |
| `scripts/packproof.py` | rewrite `proof<k>`, `cp<k>` and `inputSlots` of generated data modules |
| `scripts/merge.py` | merge a window's data, check and main modules into one |
| `scripts/regen.py`, `gen.py`, `build.py`, `run.sh` | regenerate LRAT; production generation into a scratch root; per-module `lean -o` with size, CPU and RSS (2.9 GB guard); one configuration end to end |
| `scripts/analyze.py`, `lratstats.py`, `codes.py`, `cpstats.py`, `trim.py`, `dtrim.py`, `micro.py` | `.olean` composition, hint usefulness and entropy, alternative codings, checkpoint redundancy, proof shortening, drat-trim, single-theorem kernel timings |
| `data/runs.jsonl` | every kept build (tag, window, configuration, bytes, CPU, RSS) |
| `data/offline.json` | micro-benchmark, compositions, coding, checkpoint and trimming numbers |
| `scripts/measure.py` | (Production) `lean -o` of named modules into a scratch directory: bytes, CPU, RSS (2.9 GB guard), `#print axioms` |
| `data/production_runs.jsonl` | (Production) every build of the production section, with a `_notes` line explaining the tags |
| `work/final_lean/ProofPack.lean`, `work/final_lean/LocalWindowCnfPack.lean` | (Production) the replay-data decoder (as `lean/ProofPack.lean`) and the core/soundness-data decoders, with lakefile entries |
| `milestones/10-window-aggregate/scripts/gen_lean_lrat.py --packed`, `milestones/23-k6-lean/certify/replay_k6.py gen --packed` | (Production) one packed replay module per window |
| `milestones/10-window-aggregate/scripts/gen_lean_cnfsat_packed.py` | (Production) one packed core + clause-soundness module per window |
| `work/final_lean/LratV3.lean`, `scripts/gen_lean_lrat_v3.py` | (Checker v3) the database-free checker with its soundness proof, and its generator (`replay_k7.py gen --checker v3`) |
| `scripts/pmp.py`, `scripts/pmpagg.py` | (Checker v3) stack sampling of a running `lean` with gdb, and the aggregation |
| `data/v3_runs.jsonl` | (Checker v3) every build of that section |
| `work/final_lean/LocalWindowTagsW.lean`, `work/final_lean/LocalWindowTagsSW.lean` | (Sat v2) the checker family `TagsW` (flat tables, kernel-native checker, counter table) and the share checker `TagsSW`, with their soundness proofs |
| `gen_lean_cnfsat_packed.py --sat-v2`, `gen_k7_core.py run/cnfsat --sat-v2` | (Sat v2) packed core modules checked by `TagsW.checkAllT` |
| `scripts/satv2_convert_share.py` | (Sat v2) conversion of a main share floor to `TagsSW`, for the measurement |
| `data/satv2_runs.jsonl` | (Sat v2) every build of that section |

**Reproduce.**

```sh
export STUDY=/tmp/replay-study
mkdir -p $STUDY/oleanstudy/{work,certs,lib}
lean -o $STUDY/oleanstudy/lib/ProofPack.olean milestones/26-replay-efficiency/lean/ProofPack.lean
python3 milestones/26-replay-efficiency/scripts/regen.py d012304_a4_3_6-21_3_3
cd milestones/26-replay-efficiency/scripts
NOPACK=1 ./run.sh rec 25000 3 4 16384 1 2000 d012304_a4_3_6-21_3_3 K012304A43633   # recommended
./run.sh base 25000 3 4 0 0 2000 d012304_a4_3_6-21_3_3 K012304A43633             # production
```
