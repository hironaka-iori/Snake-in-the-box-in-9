# Certificates of the new k7 keys: the H9 path, validated on five keys

Run of 29 October 2026, about 1 h, next to another agent's solver jobs on 3 cores. One `lean`
process at a time (`nice -n 15`, killed above 2.9 GB of RSS), solvers at `nice -n 19`. Every Lean
module was compiled with `lean -o` into a scratch directory listed first in `LEAN_PATH`, and deleted
after measuring. No existing `.olean` and no `LocalWindowUnsat/` file was touched; lake was not run.

**Why.** The 234 plan (`../README.md`, `../lean/README.md`) needs `allRefutedK7 : AllRefutedK7` for
the new keys of its key set: about 21.7 k keys for `keys_l416y`, 7.0 k of them H9 windows (9
directions, 7 counts, the first interior vertex uncounted, stored reversed). No H9 window had
gone through the Lean certificate path before.

## Answer

| | result |
|---|---|
| keys | five H9 keys of `../data/keys_l416y.json.gz` (the lowest-cost set when this ran), oracle solve times 0.024, 0.04, 0.08, 0.30 and 1.41 s (about the 50th, 87th, 94th, 98.8th and 99.8th percentile of its 6,968 H9 keys); `data/keys_h9five.json.gz` |
| verified | **all five**. Each `K7….refuted : Refuted (winOf ds) (boundsOf syms)` (ds = the 9 stored directions, 7 bounds), `allRefutedK7_0 : AllRefutedList dirKeysK7_0` and `allRefutedK7 : AllRefutedK7` (the premise exactly as `gen_lean_glue7.py keys` defines it) depend on **`propext`, `Classical.choice`, `Quot.sound`** only |
| encoding | the radius-4 CNF of `../k7.py encoding` (checked clause for clause on the five keys): the ball around all 8 interior vertices, counters on the 7 counted ones only. 4,469 to 4,595 variables, so the O5k checkers (14-bit words) |
| tagging | the Tags checker needs nothing new: `centresOf` takes 7 centres, and the counters of the H9 CNF are on centres 0..6. The generators had to pad `alpha` with `None` for the eighth interior vertex (one line, a no-op for every existing set) |
| memory | the clause-soundness check of an H9 core does not fit 3 GB as one declaration (2.43 GB for the smallest core, 2.79 GB for the next). New: `work/final_lean/LocalWindowTagsSplit.lean` and `gen_lean_cnfsat_packed.py --part-lits`, which check the counters by a linear `ctrOKL` and the clauses in parts. Every Cnf module then needs **1.16-1.52 GB and 9-27 s** |
| driver | `gen_k7_core.py` (cores, packed Cnf+Sat modules, chunk and aggregate modules) and `replay_k7.py` (packed replays, guarded build), validated on the five keys |
| full run (projection, `keys_l416y`) | about 2.2 G hints. **About 220-260 CPU-hours** (replays about 160, or about 130 with the 8-seed, 5-round proofs, plus 60-100 for the Cnf+Sat modules) and **about 8.5-10 GB** of `.olean`. Commands below |

## Per-key measurements

The five keys, smallest first. All modules were compiled by `../../26-replay-efficiency/scripts/measure.py`.
CPU is `wait4` user+system time of the whole `lean` run (elaboration and kernel). Bytes are file sizes.
Replays use `core_lrat` with seeds 1-2 and 1 round (the K235 setting), packed O5k with 14-bit words.

| module | variables | clauses | core (clauses / literals) | LRAT hints (lemmas) | Cnf+Sat src / `.olean` | Cnf+Sat CPU, RSS | replay src / `.olean` | replay CPU, RSS |
|---|---|---|---|---|---|---|---|---|
| `K7012031041A2555246` | 4,469 | 75,448 | 1,032 / 2,807 | 2,514 (529) | 26.1 / 50.9 KB | 9.5 s, 1.16 GB | 22.4 / 42.5 KB | 1.6 s, 0.61 GB |
| `K7012032405A4365432` | 4,469 | 75,448 | 1,625 / 4,966 | 18,796 (433) | 38.9 / 62.0 KB | 12.2 s, 1.27 GB | 88.2 / 76.8 KB | 4.6 s, 0.93 GB |
| `K7012304235A4455344` | 4,595 | 75,022 | 2,373 / 8,229 | 97,828 (1,660) | 56.6 / 73.6 KB | 15.4 s, 1.44 GB | 0.44 / 0.27 MB | 23.1 s, 1.26 GB |
| `K7012302435A6435444` | 4,469 | 75,448 | 3,114 / 11,399 | 267,690 (7,515) | 72.6 / 81.8 KB | 19.4 s, 1.52 GB | 1.47 / 0.81 MB | 58.9 s, 1.48 GB |
| `K7012314031A5453464` | 4,491 | 76,742 | 4,556 / 17,511 | 1,024,596 (26,966) | 101.4 / 102.0 KB | 26.7 s, 1.52 GB | 7.02 / 3.70 MB | 262.4 s, 2.47 GB |

- **No cycle cuts.** None of the five needed a lazy cycle cut, so the CNF is the static encoding.
- **Solver time.** Encoding, cut loop, core and Cnf generation took 0.8 to 6.7 s a key.
  Replay generation (`core_lrat` and the Lean source) took about a minute for the largest.
- **Hints against the key set's estimate.** The key set estimated 1,378, 19,770, 82,846, 269,084
  and 1,098,221 hints, which is close. Its core sizes (302 to 4,381) underestimate the small cores,
  which have at least about 1,000 clauses.
- **Shorter proofs.** `replay_k7.py measure --seeds 8 --rounds 5`, the recommendation of
  milestone 26, gives 2,514, 12,638, 84,643, 215,451 and 846,722 hints. That is **−18 %** in all
  (1,411,424 → 1,161,968), for 149 s of solver time on the five.
- **Unit costs.**
  - Replay: about **1 s + 0.23-0.26 ms per hint**. The `.olean` is about **37 KB + 3.6 B per hint**
    (3.57 B on the largest). That is above milestone 26's 2.9 B, because the O5k words are 14 bits
    wide and the clause tree of the largest has height 13.
  - Cnf+Sat: about **6 s + 1.2 ms per core literal**. The `.olean` is about 41 KB + 3.5 B per
    literal.
- **The aggregate modules are cheap.** `LocalWindowDirKeysK7_P0`, `LocalWindowDirKeysK7`,
  `LocalWindowDirUnsatK7_0` and `LocalWindowDirUnsatK7` take 0.2-0.4 s each.
- **The guarded build reproduces the measured modules.** `replay_k7.py build --out <scratch root>`
  (`guarded_lake_build.py --direct`, one job) rebuilt the ten modules in 439 s, each within 10 % of
  the times above, with peak RSS 0.57-2.36 GB.
- **Data.** Every number is in `data/h9five_runs.jsonl`, one line per key. The core JSONs are in
  `milestones/10-window-aggregate/data/lean_core_direction_k7/`.

## What changed, and why

### H9 encoding and tags (`gen_lean_sat.py`, `gen_lean_cnfsat_packed.py`)

An H9 key `(ds, syms)` has 9 directions, so `winOf ds` has 10 vertices and 8 interior vertices,
but only 7 counts.

- **Lean side.** `centresOf (winOf ds) (boundsOf syms)` takes `syms.length` = 7 centres, and the
  eighth interior vertex carries no constraint. Nothing in `LocalWindowModel`, `LocalWindowTags`
  or the bridge (`refuted_dirH`, `no_forb_H9`) changes.
- **CNF side.** `wincert.Encoding` takes one alpha entry per interior vertex. The H9 CNF of
  `../k7.py` has alpha = 7 bounds + `None`: the ball is around all 8 interior vertices, and no
  counter is built for the eighth.
  - This is sound for `Axioms`, which has no ball: every clause family is a consequence of the
    snake conditions.
  - The `ctrOK` checks refer to centres 0..6, all of which are in `centresK`.

The existing generators rebuilt the encoding from `bounds` alone, with 7 alphas for 8 interior
vertices. So `TaggedEncoding` failed on the eighth (IndexError), and the core could not have been
tagged. The fix:

- `gen_lean_sat.uncounted_centres(window, bounds)` gives `len(window) - 2 - len(bounds)`, asserted
  to be 0 or 1.
- `gen_lean_sat.process` and `gen_lean_cnfsat_packed.core_data` pad `alpha` with that many `None`.
- **Existing sets are unchanged.**
  - All 2,246 committed core JSONs pad 0 (`lean_core`, `_direction`, `_direction5`, `_k6`, `_r4`,
    `_r4b`).
  - The packed output for two K windows (K012031A42652 and K012340A26336) is byte-identical to the
    previous generator, with and without `--split`.

### Splitting the clause-soundness check (`LocalWindowTagsSplit.lean`, `--part-lits`)

The single `check : checkAll … = true` of a packed Cnf module took 21.9 s and 2.43 GB on the
smallest H9 core, and 25.5 s and 2.79 GB on the next one. The kernel keeps all caches of one
declaration until its end. Probes on the smallest core (`data/h9five_runs.jsonl` keeps the module
figures):

| piece, one `decide +kernel` each | CPU | peak RSS |
|---|---|---|
| all counters, `ctrs.all (ctrOK …)` | 14.5 s | 1.77 GB |
| … only the endpoint counter's `pw` (348 flags, about 60,000 pair comparisons) | 13.7 s | 1.69 GB |
| … the 13 other counters | 0.85 s | 0.53 GB |
| all 1,032 clauses, `ckAll …` | 6.3 s | 1.15 GB |
| decoding `raw`, `tags` and `meaning` | 1.0 s | 0.57 GB |

So the cost is the quadratic order check of the endpoint counter. The radius-4 ball around 8
centres has about 350 vertices with all neighbours inside, and every one gets an endpoint flag. On
top of that come the clause checks, at about 0.2 MB of caches per literal, with up to 17,511
literals here.

`work/final_lean/LocalWindowTagsSplit.lean` (new, core Lean, 0.6 s; `checkAll_of_parts`:
`propext`, `Quot.sound`) adds:

- **`pwL`**: strictly increasing, checked on adjacent entries. **`pw_of_pwL`** proves it implies
  `pw`, by transitivity.
- **`ctrOKL`**: `ctrOK` with `pwL` for the endpoint counter. With it come **`ctrOK_of_ctrOKL`** and
  `all_ctrOK_of_ctrOKL`.
- **`ckAll_append`**: two consecutive parts of tags and clauses, checked separately.
- **`checkAll_of_parts`**: `checkAll M cs w b tags raw` from `cs.all (ctrOKL …)` and
  `ckAll … tags raw`.

`gen_lean_cnfsat_packed.py --part-lits N` is a new path; without it the output is unchanged. It
writes:

- `raw_0 … raw_k` and `tags_0 … tags_k`, consecutive parts of at most N literals, with
  `raw := raw_0 ++ (raw_1 ++ …)` and `tags` likewise;
- `check_ctrs` (by `ctrOKL`) and `check_<i>`, one `decide +kernel` each, with
  `set_option Elab.async false` so that the parts run one after another;
- `check`, by `checkAll_of_parts` and `ckAll_append`.

The names and statements of `window`, `bounds`, `raw`, `cnf`, `tags`, `check` and `sat` are those
of the default layout, so the replays and `Tags.refuted_of_sat` use them unchanged. With N = 4000
(the default of `gen_k7_core.py`):

| core | single `check` | with parts |
|---|---|---|
| 1,032 clauses (1 part) | 21.9 s, 2.43 GB | **9.5 s, 1.16 GB** |
| 1,625 clauses (2 parts) | 25.5 s, 2.79 GB | **12.2 s, 1.27 GB** |
| 4,556 clauses (5 parts) | not run (well above 3 GB) | **26.7 s, 1.52 GB** |

The same option should help the k6-pool keys of the K7 set. Their single-check Sat modules in the
K235 build took a median of 17.8 s and up to 9.1 GB. This has not been measured.

### The driver (`gen_k7_core.py`, `replay_k7.py`)

| step | command | writes |
|---|---|---|
| keys | `gen_lean_glue7.py keys --keys K` (exists) | `LocalWindowDirKeysK7.lean`, `LocalWindowDirKeysK7_P<p>.lean`: the new keys in chunks `dirKeysK7_<c>` of 400 |
| cores | `gen_k7_core.py run --keys K --work W` | per new key: CNF (encoding + lazy cycle cuts, deleted), core (`full_core_ids`, CaDiCaL `FULL_PORTFOLIO`, as `gen_k6_core.py`), `milestones/10-window-aggregate/data/lean_core_direction_k7/<name>.json` (core ids, cycle cuts, CNF SHA256), and **`LocalWindowCnf/K7<ds>A<syms>.lean`** (packed core + `sat`, `--part-lits 4000`) |
| replays | `replay_k7.py gen --work W` | per core: CNF regenerated and SHA-checked, `core_lrat`, **`LocalWindowUnsat/K7<ds>A<syms>.lean`** (`gen_lean_lrat_o5k.py --off 5000 --fast --split --noncomputable-data --packed`, `--seg 25000 --cp 3`, the narrowest of 14-17-bit words); CNF and LRAT deleted |
| build | `replay_k7.py build` | `work/guarded_lake_build.py --direct --trust-mtime` on the generated replays and their Cnf modules (heavy jobs: `^LocalWindow(Unsat\|Cnf)\.K7`) |
| chunks | `gen_k7_core.py final --keys K` | **`LocalWindowDirUnsatK7_<c>.lean`** (per key `K7….refuted : Refuted (winOf ds) (boundsOf syms) := Tags.refuted_of_sat K7….sat K7….unsat`; `allRefutedK7_<c> : AllRefutedList dirKeysK7_<c>`) and **`LocalWindowDirUnsatK7.lean`** (`allRefutedK7 : AllRefutedK7`) |

- **Names.** Module prefix `K7`, case names `d<ds>_a<bounds>` as in the k6 set. Canonical
  directions start with `0`, so `K7…` never collides with a `K0…` module of the k6 set.
- **Key kinds.** The same code path serves the k6 and F8 keys of the set, with nothing padded.
  Only H9 keys were run here.
- **Order and resuming.** `run` takes the keys smallest estimate first (the key file's `hints`).
  It skips a key whose JSON and Cnf module exist, and `gen` skips a key whose replay exists. So
  every step resumes, and `gen --budget-hints` makes batches.
- **Where the files go.** `--out` sets the Lean root (default `work/final_lean`), and `--core` the
  JSON directory. The scratch root of this run is not committed.

## Commands for the full run

Preconditions:

- the disk holds about 12 GB (below);
- `free -g` shows at least 4 GB available per heavy job;
- `export PATH=/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin:$PATH`;
- `S` is a scratch directory outside the repository, and `K=milestones/25-k7-234/data/keys_<T>.json.gz`
  is the chosen key set.

```sh
# 0. Libraries the new modules import.  ProofPack, LocalWindowCnfPack and the O5k checkers have
#    lakefile entries; LocalWindowTagsSplit and LocalWindowDirGlue7, like every K7 module, are
#    built with --direct (no lakefile entry).
cd work/final_lean
nice -n 19 python3 ../guarded_lake_build.py --direct --trust-mtime --jobs 1 \
    ProofPack LocalWindowCnfPack LocalWindowTagsSplit LocalWindowDirGlue7 \
    LratFast2_O5k14 LratFast2_O5k15 LratFast2_O5k16 LratFast2_O5k17 \
    LratFast2F_O5k14 LratFast2F_O5k15 LratFast2F_O5k16 LratFast2F_O5k17
cd ../..

# 1. The key modules of the new keys (dirKeysK7_<c>, AllRefutedK7).
python3 milestones/25-k7-234/lean/scripts/gen_lean_glue7.py keys --keys $K

# 2. Cores and packed Cnf+Sat modules (about 2 s of solver time per H9 key, more for k6 keys).
nice -n 19 python3 milestones/25-k7-234/certify/gen_k7_core.py run --keys $K --work $S/k7core --min-disk-mb 2000

# 3. Replays in batches; repeat until `gen` writes nothing.  Proofs of 8 seeds x 5 rounds
#    (-18 % hints on the five keys).
nice -n 19 python3 milestones/25-k7-234/certify/replay_k7.py gen --work $S/k7replay \
    --seeds 8 --rounds 5 --budget-hints 50e6 --min-disk-mb 2000
python3 milestones/25-k7-234/certify/replay_k7.py build --jobs 1 --heavy-jobs 3 --rss-cap-gb 3.5

# 4. The chunk modules and the premise allRefutedK7.
python3 milestones/25-k7-234/certify/gen_k7_core.py final --keys $K
cd work/final_lean
nice -n 19 python3 ../guarded_lake_build.py --direct --trust-mtime --jobs 1 --rss-cap-gb 4 \
    --log .lake/guarded_build_k7.jsonl LocalWindowDirUnsatK7
cd ../..

# 5. The chain, its glue and the final module, as in ../lean/README.md (gen_lean_automaton7.py,
#    gen_lean_chain7.py, then gen_lean_glue7.py glue / final --tag T --bound 234).
```

Before the audit,
`grep -rlE "sorry|native_decide|^axiom" work/final_lean/LocalWindow{Cnf,Unsat}/K7* work/final_lean/LocalWindowDir*K7*.lean work/final_lean/LocalWindowTagsSplit.lean`
must print nothing. It printed nothing for the five-key run.

The five-key validation, in the same order, in a scratch root `$H` (oleans in `$H/olean`, first in
`LEAN_PATH`):

```sh
K=milestones/25-k7-234/certify/data/keys_h9five.json.gz
python3 milestones/26-replay-efficiency/scripts/measure.py --src work/final_lean --out $H/olean \
    ProofPack LocalWindowCnfPack LocalWindowTagsSplit LocalWindowDirGlue7 \
    LratCheckO5k LratFastO5k14 LratFast2_O5k14 LratFast2F_O5k14
nice -n 19 python3 milestones/25-k7-234/certify/gen_k7_core.py run --keys milestones/25-k7-234/data/keys_l416y.json.gz \
    --kinds H --work $H/work --out $H/src --fsize-mb 60 --min-disk-mb 400 \
    --only 012031041:2555246 012032405:4365432 012304235:4455344 012302435:6435444 012314031:5453464
nice -n 19 python3 milestones/25-k7-234/certify/replay_k7.py gen --work $H/work --out $H/src --fsize-mb 60 --min-disk-mb 400
python3 milestones/25-k7-234/lean/scripts/gen_lean_glue7.py keys --keys $K --out-core $H/src
python3 milestones/25-k7-234/certify/gen_k7_core.py final --keys $K --out $H/src
for M in K7012031041A2555246 K7012032405A4365432 K7012304235A4455344 K7012302435A6435444 K7012314031A5453464; do
  python3 milestones/26-replay-efficiency/scripts/measure.py --src $H/src --out $H/olean --axioms \
      LocalWindowCnf.$M:Snake9.LocalWindow.$M.sat LocalWindowUnsat.$M:Snake9.LocalWindow.$M.unsat
done
python3 milestones/26-replay-efficiency/scripts/measure.py --src $H/src --out $H/olean --axioms \
    LocalWindowDirKeysK7_P0 LocalWindowDirKeysK7 LocalWindowDirUnsatK7_0:Snake9.LocalWindow.allRefutedK7_0 \
    LocalWindowDirUnsatK7:Snake9.LocalWindow.allRefutedK7
# the same ten modules through the driver's guarded build, into $H/src/.lake
LEAN_PATH=$H/olean:work/final_lean/.lake/build/lib/lean \
    python3 milestones/25-k7-234/certify/replay_k7.py build --out $H/src --jobs 1 --heavy-jobs 1
```

`gen_lean_glue7.py keys` writes the key file's path into a doc comment. A path containing `/-`,
such as this machine's scratchpad `/tmp/claude-0/-home-…`, opens a nested comment, so the key file
must live elsewhere. Here it is in `data/`.

## Projection for a full run (`keys_l416y`)

`gen_lean_glue7.py` split gives 21,656 new keys in 55 chunks:

| kind | keys | hints (key-set estimate) | replays: CPU, `.olean` | Cnf+Sat: CPU, `.olean` |
|---|---|---|---|---|
| H9 | 6,968 | 0.15 G | about 12 h, 0.8 GB | about 20 h (9-27 s each), 0.4 GB |
| F8 | 454 | 0.14 G | about 10 h, 0.5 GB | about 2 h, 0.03 GB |
| k6 pool | 14,234 | 1.91 G | about 135 h, 6-7.5 GB (O4k keys have 13-bit words, about 2.9 B/hint) | 40-80 h (not measured with parts), 0.8 GB |
| **total** | **21,656** | **2.2 G** | **about 160 h** (about 130 h with 8 x 5 proofs), **7.3-8.7 GB** | **60-100 h, 1.2 GB** |

- **Basis of the projection.** It uses the unit costs above. The key-set hint estimates matched
  the five measured replays to within 15 % on the four larger keys; the smallest had 1.8 times
  its estimate.
- **Not counted.** The 55 chunk modules, the aggregate, the glue and the chain shards (about 160
  CPU-hours, `../lean/README.md`) are extra.
- **Core JSONs.** At about 7 bytes per core clause id they take about 170 MB for this set, so for
  a full run they belong outside git, or compressed (`--core`).
- **Disk.** About 9-10 GB of `.olean` in all, plus 1-2 GB of transient sources and proofs for a
  batch, so about 12 GB free. This machine had 0.47 GB free, so the full run cannot start here.
- **Wall time.** With 3 heavy jobs, about 3-4 days.

## Files

| file | contents |
|---|---|
| `gen_k7_core.py` | `run` (CNF, cuts, core, core JSON, packed Cnf+Sat module), `cnfsat` (rewrite Cnf modules from core JSONs), `final` (chunk modules `LocalWindowDirUnsatK7_<c>`, aggregate `LocalWindowDirUnsatK7`), `regen` (CNFs from core JSONs) |
| `replay_k7.py` | `gen` (packed O5k replays, batches), `measure` (hints only), `build` (guarded, `--direct`) |
| `data/keys_h9five.json.gz` | the five validation keys, in the key-file format |
| `data/h9five_runs.jsonl` | per key: oracle time, key-set estimates, variables, clauses, cuts, core, literals, hints (seeds 2 / 1 round and 8 / 5), Cnf+Sat and replay bytes, CPU, RSS, axioms |
| `milestones/10-window-aggregate/data/lean_core_direction_k7/*.json` | the five core JSONs (CNF regenerated from them by SHA256) |
| `work/final_lean/LocalWindowTagsSplit.lean` | `pwL`, `ctrOKL`, `ctrOK_of_ctrOKL`, `ckAll_append`, `checkAll_of_parts` |
| `milestones/10-window-aggregate/scripts/gen_lean_sat.py`, `gen_lean_cnfsat_packed.py` | `uncounted_centres` (H9 alpha padding); `--part-lits` |
