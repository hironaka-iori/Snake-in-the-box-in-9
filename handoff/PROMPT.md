# Prompt for the new machine (2026-11-02)

Paste everything below the line into Claude Code on the new machine, in a fresh clone of the branch.
(This supersedes `milestones/25-k7-234/BIG_MACHINE_PROMPT.md`.)

---

You are working on the Lean 4 project https://github.com/hironaka-iori/Snake-in-the-box-in-9, branch
`research/unconditional-241` (never push to `main`, never open a pull request). It proves bounds on a(9),
the longest snake (induced path) in the 9-cube. Lean-checked today: 191 <= a(9) <= 235. Your job: make
**234** Lean-checked end to end and, on the way, do the first fresh source-only rebuild and audit of the
235, 236 and 237 chains. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`,
no `native_decide`, no new axioms. Code, comments, commits in English. Read `handoff/README.md` first.

## 0. Setup
- Machine: Linux or macOS, 16+ cores, 64 GB RAM recommended (aggregate and final modules peak at 12-13 GB;
  replay checks 1-6 GB; shards about 1.25 GB), about 60 GB free disk.
- Lean 4.19.0 via elan (`work/final_lean/lean-toolchain`); mathlib at commit
  `c44e0c8ee63ca166450922a373c7409c5d26b00b` in a separate checkout, built or fetched with
  `lake exe cache get` (pass it to `work/spectral/chain_audit.py --mathlib-dir`); CaDiCaL (with `--lrat`)
  and drat-trim on PATH; python3. Paths in the docs like `/home/user/lean-deps/...` are the old machine's;
  substitute your own.
- Read: `README.md`; `work/spectral/README.md` (Bound 237/236/235); `milestones/10-window-aggregate/README.md`
  ("how the replays work and how to reproduce them") and `local-task-236-replays.md`;
  `milestones/23-k6-lean/certify/README.md` (how 235 was built); `milestones/25-k7-234/README.md`,
  `lean/README.md`, `certify/README.md` (sections "Final key set" and "Commands for the full run"),
  `certify/PROGRESS-B234.md` (shard build driver); `milestones/26-replay-efficiency/README.md`
  ("Production": packed encodings).

## 1. Fresh rebuild of the certified sets (237, 236, 235)
The replay modules `work/final_lean/LocalWindowUnsat/{Q,R,K}*` are generated, not committed. Regenerate
them from the committed UNSAT cores with the ORIGINAL (unpacked) pipeline exactly as documented (237:
`run_direction_replays.py --set r4b`; 236: `--set r4`; 235's K6 set: `milestones/23-k6-lean/certify/replay_k6.py`),
build `LocalWindowDirSatR4b/R4/K6` and `LocalWindowDirUnsatR4b/R4/K6`, then audit WITHOUT `--reuse`:
`python3 work/spectral/chain_audit.py --mathlib-dir <mathlib> --target UpperBound237 --log outputs/upper-bound-237-audit-<host>.log --axioms Snake9.upper_bound_237 Snake9.verified_interval_191_237`,
and likewise 236 and 235. Expect about 120 kernel-hours of replay checks plus a few CPU-hours of Sat modules.

## 2. Build 234 (tag B234, key set `milestones/25-k7-234/data/keys_best234.json.gz`)
Already committed and checked (do not regenerate unless a check fails): the k7 framework, the B234 data,
key, bridge, Sequence and Aggregate modules, the reuse glue `LocalWindowDirUnsatReuse7B234` /
`LocalWindowDirGlue7B234Reuse`, the K7 key modules `LocalWindowDirKeysK7*`, and
`work/spectral/stronger/UpperBound234.lean`. With the shards and `LocalWindowDirUnsatK7` stubbed, the chain
compiled to `upper_bound_234`. H9 (5 keys) and F8 (3 keys) certificates were validated end to end.
- **New certificates: certify the 2,815 seeds, then build the chunk modules.** The 9,784 new keys are
  not certified one by one. The seed plan `milestones/25-k7-234/certify/data/seeds234.json.gz` lists
  2,815 seed keys with widened count bounds (1.493 G hints; about 104 CPU-hours and 4.5 GB of .olean,
  about 88 h and 3.8 GB with 8 x 5 proofs). Every other key follows from its seed in the chunk modules:
  3,849 keys by L1 and 3,120 by L2 of `work/final_lean/LocalWindowFamilies.lean` (lakefile entry; build
  it in step 0 with the other libraries). See `milestones/25-k7-234/certify/README.md`, "Seeds and
  families", then follow "Commands for the full run" with
  `K=milestones/25-k7-234/data/keys_best234.json.gz` and `P=milestones/25-k7-234/certify/data/seeds234.json.gz`:
  1. `gen_k7_core.py run --keys $K --plan $P` to the end. It certifies the seeds with their widened
     bounds, then any *orphan* (a key its certified seed no longer implies) on its own; report the
     number of orphans.
  2. `replay_k7.py gen --plan $P` (packed encodings, `--part-lits` for large H9/F8 cores, 8 seeds x 5
     rounds) and `replay_k7.py build`.
     **Faster option:** `replay_k7.py gen --checker v3 --plan $P` writes the replays for the checker v3
     (`work/final_lean/LratV3.lean`; build it with `ProofPack` in step 0, `--direct`). It has the same
     module and theorem names and about half the kernel time: 0.12-0.13 against 0.21-0.26 ms per hint
     on 0.1-1.5 M-hint windows, 1.7-2.0x, and 2.3-3.5x on small windows. It also needs about 25 % less
     `.olean`. Validated end to end on 4 k6 windows, 1 F8 and 1 H9 key (standard axioms); see
     `milestones/26-replay-efficiency/README.md`, "Checker v3". Use one checker for the whole run, or
     mix them per window: the statements are identical.
  3. `gen_k7_core.py final --keys $K --plan $P`, then build the chunk modules `LocalWindowDirUnsatK7_<c>`
     (each derives its keys by one kernel `decide` per key: 0.01-0.08 s, 0.5 GB per 400-key chunk) and
     `LocalWindowDirUnsatK7`.

  `allRefutedK7 : AllRefutedK7` has the same statement as before, so the glue and `UpperBound234` are
  unchanged. Keep the key file and scratch paths free of `/-` (a doc-comment pitfall noted there).
  End with `LocalWindowDirUnsatK7` proving `allRefutedK7`.
- **Shards (792, about 160 CPU-hours, 5-12 min and <= 1.25 GB each):** generated by
  `milestones/25-k7-234/lean/scripts/shard_build7.py prepare` (byte-identical to the manifest
  `lean/data/shards7_B234.sha256`) and built as `PROGRESS-B234.md` describes. With plenty of disk you can
  prepare all of them at once and run one guarded build with many heavy jobs (cap about 2.5 GB each); the
  sweeper is only needed when disk is short.
  **Faster option (shard v2, about 27x):** the same shards checked through witness codes
  (`work/spectral/stronger/WindowAutomaton7V2.lean`, bridge `check7In_of_W`; propext and Quot.sound
  only): about 5-6 CPU-hours in all, 11-35 s and about 0.5 GB per shard, `.olean` about 13 % smaller.
  Build `WindowAutomaton7V2` into `work/spectral/.verification/chain` first, then run the driver with
  `SHARD_V2=t1` (manifest `lean/data/shards7_B234_v2.sha256`). Same module names and the same theorem
  `shard7B234_<i>_<t0>`, so nothing downstream changes and v1/v2 shards can be mixed. See
  `milestones/25-k7-234/lean/README.md`, "Shard v2".
- **Audit:** `chain_audit.py --target UpperBound234 --log outputs/upper-bound-234-audit-<host>.log --axioms
  Snake9.upper_bound_234 Snake9.verified_interval_191_234`. Write `outputs/upper-bound-234-replay-<host>.log`
  in the style of `outputs/upper-bound-235-replay-linux.log`.
- Before the audit, `grep -rlE "sorry|native_decide|^axiom"` over all new K7/B234 modules must print nothing.

## 2b. Optional after 234: the share-weighted 233 chain (tag B233)
Framework and generators: `milestones/33-233-lean/README.md`. Generic modules (core:
`WindowAutomaton6SDefs`, `WindowAutomaton6SV2`, `DirectionWindowBridge6S`, plus
`milestones/28-combined-identities/lean/CombinedShareToy.lean`; mathlib: `AggregateDirection6SConditional`
after `ShareCharge`/`ShareBridge`) compile with standard axioms; the toy chain compiles without `sorry`.
Generate with `gen_lean_automaton6s.py --set milestones/31-233-cost/data/keys233_best.json.gz --tag B233
--lam 520/1 --bits 10 --expect-range 784 --expect-bound 233` and `gen_lean_chain6s.py --tag B233`.
The instance theorem `upper_233_of_refuted6SB233` takes `AllRefuted6SB233` (6,794 plain k6 keys, 1,383
already replayed, and 262 H8 cuts), `AllRefutedShare6SB233` (490 `RefutedShare … 12 (L-1)` thresholds)
and `Floors233` (main's share16 of milestone 152, canonical7300/7304/7306 of milestone 73, share17 of
milestone 155; their statements are copied, their proofs are not on this branch). Shards: 204, about
10 s and 0.55 GB each, about 0.65 CPU-hours in all. Certificates: about 3.2 G hints (milestone 31).
The conditional 233 compiles (commit 35cff09e, `outputs/aggregate-233-conditional-chain-linux.log`).

**Discharging `Floors233`** (`milestones/33-233-lean/FLOORS.md`). Main's five floor theorems prove this
branch's copies literally: their `Snake`, `canon`, `dsOf`, `dir`, `coreAlpha`, `coreShare` and
`RefutedShare` come from modules that are byte-identical to ours or of which ours is a superset. Lean 4.19.0
and mathlib c44e0c8e are the same. `work/spectral/stronger/Floors233Bridge.lean` compiles, and its
`floors233_of_main` takes main's five statements verbatim and returns `Floors233`. Port steps:
1. Free about 0.7 GB of disk; the build needs about 0.45 GB of `.olean` files.
2. Run `python3 milestones/33-233-lean/scripts/port_main_floors.py --build-dir B --delete-sources --max-rss-gb 6.5
   --log L`. It builds the 1,042 new modules of `data/main_floor_modules.json` in order, one `lean -o` each,
   fetching the sources from main by blob sha (gh API, no git fetch). The 151 replay sources and the 73
   cases come from main's archives. Use `--only ShareComplete152`, `--only ShareComplete155` or
   `--only Share7306.Reversal` to build one part at a time. This is 2.5 to 3 CPU-hours. Main's milestone-73
   LRAT checks exceed 3 GB of RSS: `Check1` of 7300 was stopped at the 3 GB cap after 85 s.
3. Regenerate the 204 B233 shards if their `.olean` files are gone, then compile `Floors233Bridge` and
   `milestones/33-233-lean/lean/Floors233Main.lean` with `LEAN_PATH` = B, core, chain and mathlib. The second
   gives `Snake9.Floors233Port.upper_233_of_certs6SB233 : AllRefuted6SB233 → AllRefutedShare6SB233 → m ≤ 233`;
   audit its axioms.

## 3. Rules learned the hard way
- Build only with `work/guarded_lake_build.py --direct --trust-mtime`; never a plain `lake build` over many
  certificate modules. `--heavy-jobs` about (RAM_GB - 8) / 4 for replay checks with `--rss-cap-gb 6.5`; run
  aggregates and UpperBound modules alone with a high cap.
- Never recompile a base module (`LocalWindowModel`, `Lrat*`, `NatPack`, `ProofPack`, ...) after
  certificates are built: a newer timestamp makes `--trust-mtime` rebuild everything importing it. Before
  each large build, simulate staleness with `closure()`/`uptodate()` from `guarded_lake_build.py` (import via
  importlib) and check that only the expected modules are stale.
- Main theorems over 1000 segments are chunked (`gen_lean_lrat.py` `MAIN_CHUNK`); aggregates use one `refine`
  per window.
- In scratch tests, `LEAN_PATH` must list the scratch output BEFORE the production `.lake/build/lib/lean`.
- Kill processes only by PID (pgrep/pkill patterns can match your own shell). Run long builds with nohup
  and a PID file; log progress in `milestones/25-k7-234/certify/PROGRESS-<host>.md` and commit it regularly.
- Never weaken a statement to make something compile. A failing kernel check means a wrong certificate or a
  generator bug: investigate, do not skip.

## 4. Git and report
Commit generators, small generated modules that compile without `sorry`, progress notes and the
`outputs/` logs; not LRAT files or replay sources. `git pull --rebase origin research/unconditional-241`
before each push; commit only your own paths; do not edit `README.md`, `COLLABORATION.md` or `paper/`.
Report: whether `upper_bound_234` and `verified_interval_191_234` passed the axiom audit; the seeds
certified and the orphans; whether the fresh
235/236/237 audits passed; module counts, check modules, kernel-hours, peak memory, wall time, disk; any
generator fixes; anything that failed.
