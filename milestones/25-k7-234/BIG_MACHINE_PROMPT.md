# Prompt: build and audit the bound 234 on a large machine

Paste everything below the line into a Claude Code session on the large machine.

---

You are working on the Lean 4 project https://github.com/hironaka-iori/Snake-in-the-box-in-9, branch
`research/unconditional-241` (never push to `main`, never open a pull request). It proves upper bounds on
a(9), the longest snake (induced path) in the 9-cube. The Lean-checked interval is 191 <= a(9) <= 235.
Your job: make **234** Lean-checked end to end, and as a by-product do the first fresh source-only rebuild of
the 235, 236 and 237 chains. Use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):
no `sorry`, no `native_decide`, no new axioms. Code, comments and commits in English.

## 0. Machine and setup
- Needs: Linux or macOS, 16+ cores, 64 GB RAM recommended (single aggregate/final modules peak at 12-13 GB;
  replay checks 1-6 GB each), and about **60 GB free disk** (old replays in the original encoding ~21 GB,
  new packed certificates ~6-8 GB, mathlib ~6 GB, generated sources and headroom).
- Clone the branch. Install Lean 4.19.0 via elan (`work/final_lean/lean-toolchain`), mathlib at commit
  `c44e0c8ee63ca166450922a373c7409c5d26b00b` (build it or `lake exe cache get` in a mathlib checkout of that
  commit; `work/spectral/chain_audit.py --mathlib-dir <dir>` expects it), CaDiCaL (with `--lrat`) and
  drat-trim on PATH, python3.
- Read first: `README.md`, `work/spectral/README.md` (sections Bound 237/236/235), and
  `milestones/10-window-aggregate/README.md` ("how the replays work and how to reproduce them"),
  `milestones/10-window-aggregate/local-task-236-replays.md`, `milestones/23-k6-lean/certify/README.md`
  (235), `milestones/25-k7-234/README.md`, `milestones/25-k7-234/lean/README.md`,
  `milestones/25-k7-234/certify/README.md` (234 pipeline; use its "Final key set" section if present),
  `milestones/26-replay-efficiency/README.md` ("Production": packed encodings).

## 1. Rebuild the certified old sets from the committed cores (fresh source-only rebuild)
The replay modules (`work/final_lean/LocalWindowUnsat/Q*`, `R*`, `K*`) are generated and not committed.
Regenerate them from the committed UNSAT cores with the ORIGINAL (unpacked) pipeline, exactly as the docs
above describe (237 set: `run_direction_replays.py --set r4b`; 236 set: `--set r4`; 235 K6 set:
`milestones/23-k6-lean/certify/replay_k6.py`), build `LocalWindowDirSatR4b/R4/K6` and
`LocalWindowDirUnsatR4b/R4/K6`, then run the audits
`python3 work/spectral/chain_audit.py --mathlib-dir <mathlib> --target UpperBound237 --log outputs/upper-bound-237-audit-<host>.log --axioms Snake9.upper_bound_237 Snake9.verified_interval_191_237`
and the same for 236 and 235 (WITHOUT `--reuse`: this is the clean rebuild). Expected cost: about 120
kernel-hours of replay checks (34 + 67 + 19) plus a few CPU-hours of Sat modules.

## 2. Build 234
- Key set: `milestones/25-k7-234/data/keys_best234.json.gz` (11,167 keys: 7,070 k6 of which 1,383 are the
  old windows of step 1, 3,905 H9, 192 F8; lambda = 6423/1544, 13-bit potential, Bellman-Ford range 8,152 of
  8,191, bound 234 with margin 14; about 1.73 G new hints). If the repo has generated modules for this set
  under a tag (e.g. `B234`, see `milestones/25-k7-234/certify/README.md`), use them; otherwise retarget the
  generators (`milestones/25-k7-234/lean/scripts/gen_lean_automaton7.py`, `gen_lean_glue7.py` with the
  `reuse` mode and `keys --noncomputable`) to this key set under a new tag, check the generator dry run
  (lambda, range, bound 234) and the Python re-check of all transitions first.
- New certificates: `milestones/25-k7-234/certify/gen_k7_core.py run`, `replay_k7.py gen --packed --seeds 8
  --rounds 5`, `replay_k7.py build`, `gen_k7_core.py final`, then `LocalWindowDirUnsatK7` (proves
  `allRefutedK7`). Use the packed encodings (`gen_lean_lrat.py --packed`, `gen_lean_cnfsat_packed.py`,
  `--part-lits` for big H9/F8 cores). H9 was validated end to end on five keys; F8 keys have not been through
  Lean yet: validate three F8 keys first and fix the driver if needed.
- Automaton: the ~792 shards (one `decide +kernel` per (label, t1, t2), about 160 CPU-hours at 0.9-1.2 GB
  each; grouping 3 declarations saves ~11 % at ~2 GB), the Sequence, the bridge, `AggregateDirection7<tag>`,
  the reuse glue (`LocalWindowDirUnsatReuse7<tag>`, importing exactly the reused old windows), the K7 glue,
  and `UpperBound234`.
- Audit: `chain_audit.py --target UpperBound234 --log outputs/upper-bound-234-audit-<host>.log --axioms
  Snake9.upper_bound_234 Snake9.verified_interval_191_234`. Write `outputs/upper-bound-234-replay-<host>.log`
  in the style of `outputs/upper-bound-235-replay-linux.log` (module counts, check modules, kernel-hours,
  peak memory, failures).

## 3. Rules learned the hard way (follow all of them)
- Build only with `work/guarded_lake_build.py --direct --trust-mtime` (memory caps, logging, resume); never
  a plain `lake build` over many certificate modules. Set `--heavy-jobs` to about (RAM_GB - 8) / 4 for
  replay checks, with `--rss-cap-gb 6.5`; run aggregates and UpperBound modules alone with a high cap.
- Never recompile a base module (`LocalWindowModel`, `Lrat*`, `NatPack`, `ProofPack`, ...) after the
  certificates are built: a newer timestamp makes `--trust-mtime` rebuild everything that imports it. Before
  every large build, simulate staleness with `closure()`/`uptodate()` from `guarded_lake_build.py` (import
  it with importlib) and check that only the modules you expect are stale.
- Main theorems with more than 1000 segments must be chunked (`gen_lean_lrat.py` `MAIN_CHUNK`); aggregates
  use one `refine` per window (giant anonymous constructors overflow the stack).
- When testing in a scratch directory, `LEAN_PATH` must list the scratch output BEFORE the production
  `.lake/build/lib/lean`, or same-named modules silently load the production oleans.
- Kill processes only by PID (pgrep/pkill patterns can match your own shell). Run long builds with nohup and a
  PID file; record progress in `milestones/25-k7-234/certify/PROGRESS-<host>.md` and commit it regularly so
  the run can resume after an interruption.
- Never weaken a statement to make something compile; if a check fails, investigate (a failing kernel check
  means a wrong certificate or generator bug, not something to skip).

## 4. Git
Commit generators, small generated modules that compile without `sorry`, progress notes and the logs in
`outputs/`; do not commit LRAT files or replay sources (gitignored). Another session may push to the same
branch: `git pull --rebase origin research/unconditional-241` before each push and commit only your own
paths. Do not edit `README.md`, `COLLABORATION.md` or `paper/`; report the results instead.

## 5. Report
Whether `upper_bound_234` and `verified_interval_191_234` passed the axiom audit; whether the fresh 235/236/
237 audits passed; module counts, check modules, kernel-hours, peak memory, wall time and disk; any
generator fixes; anything that failed.
