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

## Final key set (`keys_best234`, tag B234; 31 October)

This is the set the 234 build uses: `../data/keys_best234.json.gz`, 11,167 keys at λ = 6423/1544,
range 8,152 of 8,191, bound 234. The chain is retargeted to it (`../lean/README.md`, "Retarget to the
final key set"). Its shards are being built (`PROGRESS-B234.md`).

**What still has to be certified.** These are the keys of `LocalWindowDirKeysK7` (committed,
`gen_lean_glue7.py keys --keys ../data/keys_best234.json.gz --noncomputable`): 25 chunks of 400 in 3
part modules. The other 1,383 keys are the old Q/R/K windows, proved by
`LocalWindowDirUnsatReuse7B234`.

| kind | new keys | hints (key-set estimate) | of which measured | core clauses |
|---|---|---|---|---|
| k6 pool | 5,687 | 1.567 G | 0.376 G | 8.26 M |
| F8 | 192 | 0.089 G | 0.013 G | 0.56 M |
| H9 | 3,905 | 0.077 G | 0.010 G | 1.78 M |
| **total** | **9,784** | **1.733 G** | 0.399 G | **10.61 M** |

67 keys have more than 5 M hints (the largest has 12.0 M). The k6-pool keys carry 90 % of the hints.

**F8 validated** (first F8 keys through Lean). The three keys of `data/keys_f8three.json.gz` are
about the 10th, 38th and 84th percentile of the 192 F8 keys. They went through `gen_k7_core.py run`,
`replay_k7.py gen` (packed O5k, 14-bit words, seeds 2, 1 round), `gen_lean_glue7.py keys` and
`gen_k7_core.py final`. Every module was compiled with `measure.py` into scratch.

- **Result.** Each `K7….refuted : Refuted (winOf ds) (boundsOf syms)` (8 directions, 7 counts),
  `allRefutedK7_0` and `allRefutedK7 : AllRefutedK7` depend on **`propext`, `Classical.choice`,
  `Quot.sound`** only. So do the three `sat` and the three `unsat`.
- **Keys.** The three `(ds, syms)` pairs are verbatim entries of `dirKeys7B234` and of the B234
  `dirKeysK7`, so the statements are exactly the ones the glue `allRefuted7B234_of_reuse` merges.
- **Cuts.** One key needed 5 lazy cycle cuts. These are the first cuts on the k7 path, and they
  pass through unchanged.
- **Driver.** No change was needed.
- **Data.** `data/f8three_runs.jsonl`; core JSONs in
  `milestones/10-window-aggregate/data/lean_core_direction_k7/`.

| module | core / literals | hints (8 × 5 seeds/rounds) | Cnf+Sat CPU, RSS, `.olean` | replay CPU, RSS, `.olean` |
|---|---|---|---|---|
| `K701231450A5263633` | 1,161 / 3,307 | 5,455 (2,719) | 10.3 s, 1.24 GB, 52 kB | 1.9 s, 0.65 GB, 48 kB |
| `K701203104A6325635` | 2,805 / 10,677 | 227,042 (216,171) | 17.1 s, 1.41 GB, 77 kB | 42.5 s, 1.38 GB, 663 kB |
| `K701234125A6334266` | 3,283 / 13,012 | 576,056 (457,879) | 19.4 s, 1.34 GB, 84 kB | 95.3 s, 1.42 GB, 1,599 kB |

So F8 replays cost about 0.17–0.19 ms and 2.8–2.9 B per hint, like the packed k6 windows of
milestone 26.

**Budget of the certificates.** The unit costs are measured:

| item | unit cost |
|---|---|
| replay `.olean` | 37 kB per window, plus 2.8 B/hint (k6), 2.9 (F8) or 3.6 (H9) |
| replay CPU | 1 s per window, plus 0.22 ms/hint |
| Cnf+Sat `.olean` | 41 kB per window, plus 3.5 B per core literal (about 3.6 literals per core clause) |
| Cnf+Sat CPU | 6 s per window, plus 1.2 ms per core literal |

| | CPU | `.olean` |
|---|---|---|
| replays (k6 / F8 / H9) | 97 / 5 / 6 h = **109 h** | 4.60 / 0.26 / 0.42 GB = **5.28 GB** |
| Cnf+Sat modules (k6 / F8 / H9) | 19 / 1 / 9 h = **29 h** | 0.34 / 0.02 / 0.18 GB = **0.53 GB** |
| chunk modules `LocalWindowDirUnsatK7_<c>` (25) and `LocalWindowDirUnsatK7` | minutes | about 0.02 GB |
| `.ilean` | — | 0.05 GB (none with `guarded_lake_build.py --no-ilean`) |
| **total for the certificates** | **about 140 CPU-hours** (plus the solver time of the cores and proofs) | **about 5.9 GB** |

- **Proof sizes.** With `--seeds 8 --rounds 5`, hints fall by about 18 % (−5 % to −50 % on the
  three F8 keys), so the replays take about 4.4 GB and 90 h.
- **Core JSONs.** About 0.07 GB, if kept on this disk.
- **Transient.** One batch of `replay_k7.py gen --budget-hints 50e6`: replay sources at about
  5 B/hint (0.25 GB), plus a raw CaDiCaL proof of at most `--fsize-mb` (0.7 GB). So **at least
  1 GB** must be free besides the `.olean` files.

**Rest of the chain (B234).** These figures are measured on the scratch compile. The 792 shards
take 0.167 GB without `.ilean`; this machine is building them now. The non-shard modules take
about 0.04 GB: Sequence 3.8 MB, bridge 4.5 MB, key, reuse and glue modules 4.5 MB, aggregate,
`UpperBound234`, and `LocalWindowDirKeysK7` 1.6 MB. The data module (20.9 MB) is already built.
`UpperBound234` maps 11.4 GB of oleans when it runs.

**Disk still missing on this machine.**

- **Free space.** About 0.43 GB on 31 October, after the scratch of this run was deleted. The
  shards use about 0.17 GB of it. The rule of this run keeps 0.25 GB free.
- **What is missing.** Once the shards are built, nothing is left for certificates. They need
  about **5.9 GB** of `.olean`, **≥ 1 GB** of transient space, 0.07 GB of core JSONs and 0.04 GB
  for the remaining chain modules. So **about 7.0 GB of free disk is still missing** (6.0 GB with
  the 8 × 5 proofs).
- **Where it could come from.** Deleting the 219 window oleans that the chain does not need
  (`unneeded_oleans.txt`, 0.28 GB) does not change the conclusion. Re-replaying the old Q/R
  windows with the packed encoding would free about 17.9 GB (see "Disk on this machine" below).
  That replaces existing oleans, so it is the owner's decision.

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

## Disk on this machine (29 October, second run)

**Which window oleans the 234 chain needs.**

- Method: the import closure of `UpperBound234` (`gen_lean_glue7.py final --reuse`,
  `../lean/README.md`). The import lists were read from every `.olean` of
  `work/final_lean/.lake/build/lib/lean` (54,085 files), of the 235 chain and of the k7 scratch
  oleans, by `readModuleData`. Modules that are not compiled yet were added from their generated
  sources.
- Result: the chain needs **every** `Q` (237), `R` (236) and `K` (235) window, because all 1,383
  keys of those sets are keys of every key set in `../data`.

| | window oleans | windows | du |
|---|---|---|---|
| needed: `LocalWindowUnsat` `Q` / `R` / `K` | 16,386 / 21,450 / 13,186 | 387 / 361 / 635 | 8.27 / 10.24 / 2.19 GiB |
| needed: `LocalWindowCnf` + `LocalWindowSat`, Q+R+K | 2,766 | 1,383 | 1.10 GiB |
| **not needed**: `LocalWindowCnf` `C*`, `LocalWindowSat` `C*` | 22 + 22 | 22 | 128 + 114 MiB |
| **not needed**: `LocalWindowUnsat` `D*` | 175 | 175 | 21 MiB |
| **not needed, total** (`unneeded_oleans.txt`, not deleted) | 219 | | **263 MiB (0.28 GB)** |

So the not-needed oleans break down as 0 for Q-only (237), 0 for R (236) and 0 for K (235).

**What the full 234 build needs** (`keys_l416y` projection above, chain L417d sizes):

| item | basis | disk |
|---|---|---|
| new certificates: packed replays and packed Cnf+Sat | projection above (7.3-8.7 + 1.2 GB) | 8.5-9.9 GB |
| their `.ilean` | 0.8 % of the `.olean` in the existing build | 0.07-0.08 GB |
| chunk modules `LocalWindowDirUnsatK7_<c>` and aggregate | about 2 KB per key (estimate) | 0.04 GB |
| `LocalWindowDirKeysK7` and the chain's `LocalWindowDirKeys7<T>` | 0.15 KB per key `noncomputable`, 2.25 KB as `def` (the chain keys are written as `def`) | 0.05-0.10 GB |
| data, bridge, Defs/Bridge7/Aggregate7Conditional | 32 + 3 + 3 MB measured | 0.04 GB |
| 792 shards | 23.7 KB + 1.33 KB per `decide` (fit to the 5 compiled shards, within 0.1 %), 111,366 `decide`s | 0.17 GB |
| Sequence, Aggregate, reuse modules, glue, `UpperBound234` | measured (`../lean/README.md`) | 0.01 GB |
| core JSONs, if kept on this disk | above | 0.17 GB |
| transient: the sources and proofs of one batch before sweeping, and 46 MB of chain sources | above | 1-2 GB |
| **total** | | **10.0-12.5 GB** |

**It does not fit.** About 0.43-0.47 GB was free during this run. Deleting the unneeded oleans
adds 0.28 GB, so about 0.7-0.75 GB would be free. With the 400 MB floor of the resource rules,
the build needs 10.4-12.9 GB, so about 9.7-12.2 GB are missing.

**Where the space is.** The old replays use far more bytes per hint than the packed encoding.
Hints are counted from the replay headers.

| set | hints | du | B/hint | packed, about 2.9 B/hint + 37 KB a window (milestone 26) |
|---|---|---|---|---|
| `Q` (237) | 0.303 G | 8.27 GiB | 29.3 | about 0.89 GB |
| `R` (236) | 0.373 G | 10.24 GiB | 29.5 | about 1.09 GB |
| `K` (235) | 0.223 G | 2.19 GiB | 10.6 | about 0.67 GB |

- Re-replaying `Q` and `R` with the packed generator would free about 17.9 GB. The cost is
  about 40 CPU-hours of replay at about 0.21 ms per hint, plus the regeneration of the proofs.
- That would leave about 18.6 GB free, which is enough for the build.
- This was not tried on `Q`/`R` cores, which use the older encodings.
- It means replacing existing oleans window by window, which is a decision for the owner of
  the build.

## Files

| file | contents |
|---|---|
| `gen_k7_core.py` | `run` (CNF, cuts, core, core JSON, packed Cnf+Sat module), `cnfsat` (rewrite Cnf modules from core JSONs), `final` (chunk modules `LocalWindowDirUnsatK7_<c>`, aggregate `LocalWindowDirUnsatK7`), `regen` (CNFs from core JSONs) |
| `replay_k7.py` | `gen` (packed O5k replays, batches), `measure` (hints only), `build` (guarded, `--direct`) |
| `data/keys_h9five.json.gz` | the five validation keys, in the key-file format |
| `unneeded_oleans.txt` | the 219 window oleans (with their `.ilean`, `.hash`, `.trace` files) that the 234 chain does not import; nothing was deleted |
| `data/h9five_runs.jsonl` | per key: oracle time, key-set estimates, variables, clauses, cuts, core, literals, hints (seeds 2 / 1 round and 8 / 5), Cnf+Sat and replay bytes, CPU, RSS, axioms |
| `milestones/10-window-aggregate/data/lean_core_direction_k7/*.json` | the core JSONs of the five H9 and three F8 validation keys (CNF regenerated from them by SHA256) |
| `data/keys_f8three.json.gz`, `data/f8three_runs.jsonl` | the three F8 validation keys of the final set and their measurements (31 October) |
| `PROGRESS-B234.md` | the production shard build of the B234 chain on this machine |
| `work/final_lean/LocalWindowTagsSplit.lean` | `pwL`, `ctrOKL`, `ctrOK_of_ctrOKL`, `ckAll_append`, `checkAll_of_parts` |
| `milestones/10-window-aggregate/scripts/gen_lean_sat.py`, `gen_lean_cnfsat_packed.py` | `uncounted_centres` (H9 alpha padding); `--part-lits` |
