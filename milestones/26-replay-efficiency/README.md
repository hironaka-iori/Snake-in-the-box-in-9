# Replay efficiency: `.olean` bytes and kernel time per LRAT hint

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
this README.

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

## What this does not cover

- **Cnf/Sat modules.** These are not studied here. `raw` is a literal `List (List Nat)`: the
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
