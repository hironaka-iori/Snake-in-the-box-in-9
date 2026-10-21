# Certifying the six-centre bound 235: state and build plan

Run of 21 October 2026, next to the R4 replay build (`guarded_lake_build.py --heavy-jobs 3`).
Solvers ran at `nice -n 19` on one core, one at a time. Lean modules were compiled one at a
time at `nice -n 19`, each under 2.5 GB RSS, with the oleans in the scratchpad. No
`LocalWindowUnsat/K*` replay source was written into the repository: the disk had about 1.8 GB
free.

## What the chain is

```
upper_bound_235 : Snake m → m ≤ 235                       (work/spectral/stronger/UpperBound235.lean)
 ├─ upper_235_of_refuted6K235 : AllRefuted6K235 → …        (AggregateDirection6K235, gen_lean_chain6.py)
 │    └─ tables6K235, the 204 shards, the cover, keysOK6    (gen_lean_automaton6.py --tag K235 --lam 4/1)
 └─ allRefuted6K235 : AllRefuted6K235                       (the 1,287 keys of keys_235.json)
      = allRefuted6K235_of_parts                            (LocalWindowDirGlue6K235, one kernel merge)
          allRefuted237   358 keys from dirKeysR4b          (LocalWindowDirUnsatR4b, already replayed)
          allRefuted236   294 keys from dirKeysR4           (LocalWindowDirUnsatR4, being replayed)
          allRefutedK6    635 new keys, dirKeysK6           (LocalWindowDirUnsatK6, this directory)
```

`Refuted (winOf ds) (boundsOf syms)` does not mention the number of centres or the radius. So
an exclusion that the 236/237 sets already prove is a key of the six-centre list as it
stands; the glue only does list bookkeeping.

## State

| item | state |
|---|---|
| glue, `work/final_lean/LocalWindowDirGlue6.lean` | compiles; `allRefuted_of_pick`, `allRefuted_of_pick3`, `allRefuted_of_merge`, `allRefuted_of_merge3`: axioms `propext`, `Quot.sound` |
| toy instance, `LocalWindowDirGlue6Toy.lean` | compiles; `allRefuted6Toy_of_parts` (pick witnesses) and `allRefuted6Toy_of_parts'` (merge tags): `propext`, `Quot.sound` |
| K235 instance, `LocalWindowDirGlue6K235.lean` | compiles (5 s, 0.75 GB); `merge6K235_ok` checks the 1,287 tags (358 / 294 / 635) by one `decide +kernel`; `allRefuted6K235_of_parts : AllRefuted237 → AllRefuted236 → AllRefutedK6 → AllRefuted6K235`: `propext`, `Quot.sound` |
| keys, `LocalWindowDirKeysK6.lean`, `LocalWindowDirKeys6K235.lean` | compile (5 s and 9 s) |
| the 635 UNSAT cores | **complete**: every key of `dirKeysK6` (equal as a set to keys_235.json minus dirKeysR4b and dirKeysR4) has its core JSON in `milestones/10-window-aggregate/data/lean_core_direction_k6/`, an entry in `_summary.json` (`missing: []`), a `LocalWindowCnf/K*.lean` with exactly `len(core_ids)` clauses and the right `winOf`/`boundsOf`, a `LocalWindowSat/K*.lean`, and a conjunct in `LocalWindowDirSatK6.lean`. No file is truncated. 1,250,171 core clauses; at most 3,914 variables, so no key needs the O5k checkers (619 use offset 4000, 16 use 3000) |
| Cnf/Sat modules compiled | seven pairs (the six smallest cores, 14 to 86 clauses, and a median core of 1,534 clauses): all compile; every `sat` has axioms `propext`, `Classical.choice`, `Quot.sound`. Earlier (previous run): eleven Cnf and six Sat modules |
| the largest Sat module (`K01203A3552`, 5,688 clauses) | passes 2.5 GB after 24 s and was stopped. The R4 sets had Sat modules up to 9.25 GB (`R012301A24623`), so this is expected: see the Sat build below |
| sample replays (previous run, scratchpad) | `K012034A54254` (115,256 hints, 8 modules) and `K0123042A264363` (382,195 hints, 21 modules) compile; `unsat`: `propext`, `Classical.choice`, `Quot.sound` |
| `LocalWindowDirUnsatK6.lean`, `work/spectral/stronger/UpperBound235.lean` | generated (`gen_k6_core.py final`), not compiled: they import the replays and the K235 chain |

## Hints of the replays

The replay of a key is `gen_lean_core.core_lrat` on its core (CaDiCaL, seeds 1 and 2, one
round, the shortest trimmed proof). That is deterministic, so `replay_k6.py measure` (the same
call, no Lean files) gives the exact hint count of every replay. `core_lrat_hints.jsonl` has
it for all 635 keys.

| | value |
|---|---|
| replays measured | **635 of 635** (each one regenerated its CNF from the core JSON with the recorded SHA256, and CaDiCaL refuted the core) |
| hints in total | **223,208,300** (4,621,692 lemmas) |
| median / largest | 72,223 / 6,802,090 (`K01203A3552`); the 10 largest hold 43.6 M |
| by size | 351 cases under 0.1 M hints (8.8 M in all); 218 from 0.1 M to 1 M (75.8 M); 55 from 1 M to 3 M (92.1 M); 11 above 3 M (46.6 M) |
| kernel time | **about 26 kernel-hours** at 0.42 ms per hint |

The estimates were too high: 384 M in `_summary.json` (proofs of the full CNFs, 1.7 times the
measured count) and 294 M in `../full_product/README.md` (fit on solve times, 1.3 times). The
plan below uses the measured counts.

## Disk

Measured ratios:

| module kind | sample | ratio |
|---|---|---|
| replay `.olean` per hint | the two K samples (checkpoints packed): 7.98 and 8.66 B; the 310 built R4 replays (unpacked): 11.5 B overall, 7.7 to 12.8 B on the large ones | **8.5 to 11.5 B/hint** |
| replay `.ilean` per hint | R4 replays | 0.14 B |
| replay sources per hint | the two K samples | 4.8 and 6.0 B (deleted once built, see `sweep`) |
| Cnf `.olean` / source | 15 K modules: 10.6 (largest) to 28 (tiny); the 361 R Cnf modules: 14.2 | 12.5 to 14.2 |
| Sat `.olean` / source | 10 K modules: 2.5 to 3.4; the 361 R Sat modules: 2.3 | 2.3 to 3.4 |

Estimate for the whole K build (MB = 2^20 bytes):

| part | estimate |
|---|---|
| 635 replays, `.olean` (223 M hints × 8.5 to 11.5 B) | 1,810 to 2,450 MB (about 2,130 at 10 B) |
| replays, `.ilean` | 30 MB |
| replays, the sources that stay (main and check modules; data sources swept) | about 50 MB |
| 635 Cnf `.olean` (27.8 MB of sources × 12.5 to 14.2) | 350 to 395 MB |
| 635 Sat `.olean` (41.3 MB of sources × 2.3 to 3.4) | 95 to 140 MB |
| automaton (data, 204 shards of about 40 kB, sequence, bridge), glue, keys, and a fresh chain build directory for the audit | about 130 MB |
| **persistent total** | **2.5 to 3.2 GB (about 2.8 GB)** |
| transient: one generation batch of sources (20 M hints × 6 B) plus one LRAT and CNF | about 250 MB |

With a 500 MB floor, the build needs **about 3.7 GB free** before it starts (4.0 GB at the
upper ratios). The disk had 1.8 GB free, with the R4 replay build still writing.

## Build plan

All commands from the repository root unless stated. `S` is a scratch directory outside the
repository. Every step resumes: a module whose `.olean` is newer than its source and imports is
skipped (`--trust-mtime`), and `gen` skips a case whose main module exists.

### 0. Preconditions

- `df -m /` shows at least 3,700 (better 4,000) MB free (see above). With 1.8 GB free this is not met. The
  1.5 GB of `LocalWindowUnsat/C*` oleans are not in the 235 closure, but they are in the 238 to
  241 audits, so freeing them is a decision for whoever owns those audits.
- The R4 replay build is finished: `LocalWindowDirUnsatR4` (`allRefuted236`) needs all 732
  replays. `LocalWindowDirUnsatR4b` (`allRefuted237`) is built.
- `free -g` shows at least 6 GB available before each guarded build. Never run a plain
  `lake build`.
- `export PATH=/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin:$PATH` (Lean 4.19.0, `lean`
  and `lake` for the guarded builds and the audit).

### 1. Cnf and Sat modules (before the replays: every replay's `Data0` imports its Cnf module)

```
cd work/final_lean
nice -n 19 python3 ../guarded_lake_build.py --direct --trust-mtime \
    --jobs 1 --heavy 'LocalWindowSat\.K' --heavy-jobs 2 --min-free-gb 6 --rss-cap-gb 10 \
    --log .lake/guarded_build_k6sat.jsonl \
    LocalWindowDirSatK6 LocalWindowDirGlue6K235
```

- 635 Cnf modules (about 10 s each, under 1 GB) and 635 Sat modules. The Sat modules of
  cores above about 1,600 clauses pass 2.5 GB, and the largest may need about 9 GB, as in the
  R4 sets (748 Sat modules: 7.1 CPU-hours, 239 above 2.5 GB, 6 above 6 GB). Run this step
  alone, not next to a replay build with three heavy jobs.
- About 6 CPU-hours, 3 hours wall with two jobs.
- `LocalWindowDirSatK6` gives `allRefutedK6_of_unsat : AllUnsatK6 → AllRefutedK6`;
  `LocalWindowDirGlue6K235` gives `allRefuted6K235_of_parts`.

### 2. Replay generation, build and sweep, in batches

The checkpoints of the data modules are packed as they are written (`replay_k6.gen` calls
`pack_checkpoints.rewrite`, so `cp<k>` becomes `Snake9.NatPack.unpackL [...]`; for a data
module written by hand, `python3 milestones/10-window-aggregate/scripts/pack_checkpoints.py
--dirs K…` does the same). Repeat the three commands until `gen` writes nothing:

```
cd milestones/23-k6-lean/certify
nice -n 19 python3 replay_k6.py gen --work $S/k6replay --budget-hints 20e6 --min-disk-mb 1000
python3 replay_k6.py build --heavy-jobs 3 --min-free-gb 6 --rss-cap-gb 6.5
python3 replay_k6.py sweep
```

- `gen` takes the cases smallest first. For each one it regenerates the CNF from the core JSON
  (checked by SHA256), runs `core_lrat` (one core, `nice -n 19`), writes
  `work/final_lean/LocalWindowUnsat/K<…>.lean` and `K<…>/{Data,Check}*.lean` through
  `gen_lean_lrat.py --off 3000|4000 --fast --split` (word widths 13 to 17, the narrowest that
  fits), packs the data modules, appends to `$S/k6replay/replay_gen.jsonl`, and deletes the CNF
  and the LRAT. A batch of 20 M hints is about 110 MB of sources; `--min-disk-mb` stops it
  before the disk runs low.
- `build` runs `work/guarded_lake_build.py --direct --trust-mtime` on the cases generated so
  far, with the check modules as the heavy jobs; log `work/final_lean/.lake/guarded_build_k6.jsonl`.
  The R4 checks averaged 2.4 GB and peaked at 6.3 GB.
- `sweep` deletes `LocalWindowUnsat/K*/Data*.lean` whose `.olean` is built and newer, as the
  R4 sweep does. Imports only need the `.olean`, and the guarded build treats such modules as
  prebuilt. The check sources and the main modules stay, so the replays can be rebuilt from the
  data JSON at any time.
- Time: about 26 kernel-hours at 0.42 ms per hint (the 237 rate), so about 9 to 11 hours
  with three heavy jobs.

### 3. The replay aggregate

```
cd work/final_lean
nice -n 19 python3 ../guarded_lake_build.py --direct --trust-mtime --jobs 1 --min-free-gb 6 \
    --rss-cap-gb 6.5 --log .lake/guarded_build_k6.jsonl LocalWindowDirUnsatK6
```

`LocalWindowDirUnsatK6.allRefutedK6 : AllRefutedK6` (635 `unsat` theorems and
`allRefutedK6_of_unsat`). `gen_k6_core.py final --tag K235 --bound 235` regenerates this module and
`UpperBound235.lean`.

### 4. The automaton and the chain modules

```
cd milestones/23-k6-lean/scripts
python3 gen_lean_automaton6.py --keys ../full_product/keys_235.json --tag K235 --lam 4/1
python3 gen_lean_chain6.py --tag K235
python3 ../certify/gen_k6_core.py glue --tag K235
```

- Without `--provisional` now that every key has a replay. The generator re-checks all
  6,015,223 transitions in Python and writes `work/final_lean/LocalWindowDirKeys6K235.lean`
  (the same keys, so only its header changes), `data/auto6_K235.json`, and in
  `work/spectral/stronger/`: `WindowAutomaton6K235Data.lean`, the 204 shards
  `WindowAutomaton6K235Shard<s>_<c>.lean`, `WindowAutomaton6K235Sequence.lean`,
  `DirectionWindowBridge6K235.lean` and `AggregateDirection6K235.lean`. Expected: potential range
  5 (3 bits), C = 29, bound 235.
- `glue` asserts that `LocalWindowDirKeys6K235.lean` still matches keys_235.json and that the
  three sources are in the order of the key list, and rewrites `LocalWindowDirGlue6K235.lean`.
  Recompile the keys and glue modules (step 1 command, `--trust-mtime` picks up the change).

### 5. The 204 shards and the chain, then the audit

The shards are core Lean but live in `work/spectral/stronger`, so `chain_audit.py` compiles them
with the rest of the chain (one Lean process at a time, against the built core in
`work/final_lean/.lake`):

```
python3 work/spectral/chain_audit.py --mathlib-dir /home/user/lean-deps/mathlib4 \
    --target UpperBound235 --build-dir $S/chain235 \
    --log outputs/upper-bound-235-audit-linux.log \
    --axioms Snake9.upper_bound_235 Snake9.verified_interval_191_235
```

- The chain is `WindowAutomaton6Defs`, `DirectionWindowBridge6`, `AggregateDirection6Conditional`,
  the data module, the 204 shards (one `decide +kernel` per label, `Elab.async false`, 1.9 to
  2.0 GB and about 2 minutes each: **about 7 CPU-hours**), the sequence module (52 prefix checks
  of the shape cover, 1.1 GB), the bridge (the cover row by row, minutes), the aggregate, and
  `UpperBound235`.
- The shards can run next to a replay build: each one stays near 2.0 GB.
- If the run stops, resume with `--reuse` (development only). The final audit is one run
  without `--reuse`, so it recompiles the chain, shards included (about 8 hours in all).
- The audit passes when both theorems depend only on `propext`, `Classical.choice` and
  `Quot.sound`. Before it, check the generated sources:
  `grep -rlE "sorry|native_decide|^axiom" work/final_lean/LocalWindow{Cnf,Sat,Unsat}/K* work/final_lean/LocalWindowDir*K6*.lean work/final_lean/LocalWindowDir*6K235.lean work/spectral/stronger/*6K235*.lean work/spectral/stronger/UpperBound235.lean`
  must print nothing.

## Files

| file | contents |
|---|---|
| `gen_k6_core.py` | `run`: cores, Cnf and Sat sources of the 635 new keys; `finish`: `_summary.json`, `LocalWindowDirKeysK6`, `LocalWindowDirSatK6`; `glue --tag T`: `LocalWindowDirGlue6<T>`; **`final --tag T --bound N`**: `LocalWindowDirUnsatK6` and `UpperBound<N>`; `regen`: the CNFs |
| `replay_k6.py` | `gen` (with **`--budget-hints`** for batches), `measure`, `build` (**only the generated cases**, own log), **`sweep`** |
| `core_lrat_hints.jsonl` | the measured hints of the 635 replays (`case`, `module`, `est_hints`, `hints`, `lemmas`, `producer`) |
| `work/final_lean/LocalWindowDirGlue6{,Toy,K235}.lean` | the glue, its toy instance and the K235 instance |
| `work/final_lean/LocalWindowDir{KeysK6,SatK6,UnsatK6}.lean` | the new keys, the Sat aggregate, the replay aggregate |
| `work/spectral/stronger/UpperBound235.lean` | `upper_bound_235`, `verified_interval_191_235` |
