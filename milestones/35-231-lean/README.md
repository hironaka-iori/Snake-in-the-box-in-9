# The conditional 231 chain (context shares, milestone 35)

Run of 15 November 2026. The design and the generic Lean framework are in [DESIGN.md](DESIGN.md). This file
covers the generated part: the generators, the dry run and scratch build on the certificate plan of
`milestones/28-combined-identities/certplan231.py`, and the certificate driver.

**Status.** **The conditional 231 is Lean-checked on the real plan, in a scratch build.** On the plan
`certplan231_15268_27_dual` (λ_t = 15268/27, 15-bit potential) every generated module compiled for real,
with no stub: the 204 shards, the keys, data, Sequence, bridge (k6, H8, share and both ctx covers) and
aggregate modules. The audit module prints

```
Snake9.upper_231_of_refuted6SCL15268Q27 : Snake9.LocalWindow.AllRefuted6SL15268Q27 →
  Snake9.LocalWindow.AllRefutedShare6SL15268Q27 →
    Snake9.LocalWindow.AllRefutedCtx6SCL15268Q27 →
      Snake9.DirectionWindow6S.Floors233 → ∀ {m : ℕ}, Snake9.Snake m → m ≤ 231
'Snake9.upper_231_of_refuted6SCL15268Q27' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No module printed `declaration uses 'sorry'`; no generated source contains `sorry`, `native_decide` or
`axiom`. The premises are the certificate lists (plain + H8, 5-window share, ctx 7 + ctx 8) and the floors.
`Floors233` is already discharged (`Floors233Port.floors233`, milestone 33). The certificate lists are not:
see [What is still missing](#what-is-still-missing-for-the-unconditional-231). Five real ctx certificates
(ctx 7 and ctx 8, 2,177 to 8.3 M replay hints) were produced by the new driver `certify/cert231.py` and
compiled (clause-soundness module + checker-v3 replay module each), and a glue test turns them into the
plan's `RefutedCtx7` / `RefutedCtx8` statements.

Everything was built into `/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/b231/build` (sources in `…/b231/src`, certificate work in `…/cw`), reading the
existing `.olean` files of the core (`work/final_lean/.lake/build/lib/lean`) and the 233 chain
(`work/spectral/.verification/chain`) through `LEAN_PATH`, as `build_toy.sh` does. No lake state, no
audited module and no existing `.olean` was touched. The only new file under `work/` is the source
`work/spectral/stronger/DirectionWindowBridge6SCChunks.lean`.

## Files

| file | contents |
|---|---|
| `scripts/gen_lean_automaton6sc.py` | plan → keys, data, 204 shards, Sequence. Verifies the plan independently (below) |
| `scripts/gen_lean_chain6sc.py` | summary → k6 cover parts `…R<g>`, H8 + share cover `…S`, ctx covers `…C`, bridge, aggregate, audit module |
| `scripts/build231.py` | scratch build of a target and its generated/framework imports, in dependency order, ≤ `--jobs` `nice -n 10 lean`; resumable; jsonl log of wall s, CPU s, peak RSS, `.olean` bytes; disk floor and RSS cap |
| `work/spectral/stronger/DirectionWindowBridge6SCChunks.lean` | new framework module (core Lean, 90 lines): `keyLevel_mono`, `shareRowOK_mono`, `shareCover_chunks`, `ctxCover_chunks` (see "Problems found") |
| `certify/cert231.py` | certificate driver (ctx, new 5-window share and new plain keys of the plan) |
| `certify/cores/*.json.gz` | core JSONs of the 5 test ctx certificates |
| `certify/data/*231_certplan231_15268_27_dual.jsonl` | records of the test certificates (cores, cnf, replay, build) |
| `data/auto6sc_L15268Q27.json` | summary of the generation (read by `gen_lean_chain6sc.py`) |
| `data/shards6sc_L15268Q27.sha256` | sha256 of the data module and the 204 shards (not committed, regenerated) |

The generators import the 233 generators (`milestones/33-233-lean/scripts/gen_lean_automaton6s.py`) for
their helpers and do not modify them; no audited 233 module was touched.

## How to regenerate

```
P=milestones/28-combined-identities/data/certplan231_15268_27_dual.json.gz   # any plan of certplan231.py
T=L15268Q27                                                               # tag of the identifiers
OUT=/some/scratch/src
python3 milestones/35-231-lean/scripts/gen_lean_automaton6sc.py --plan $P --tag $T --dry-run      # verify only, 7 s
python3 milestones/35-231-lean/scripts/gen_lean_automaton6sc.py --plan $P --tag $T \
    --out-stronger $OUT --out-core $OUT --sha256 milestones/35-231-lean/data/shards6sc_$T.sha256
python3 milestones/35-231-lean/scripts/gen_lean_chain6sc.py --tag $T --out-stronger $OUT
python3 milestones/35-231-lean/scripts/build231.py --src $OUT --build /some/scratch/build --jobs 2 Audit6SC$T
```

`--shards 0_1,15_3 --stub-shards` writes `sorry` stubs for the other shards (scratch only). A new plan
(another λ, ctx-7-only, other keys) is a rerun of these four commands with a new `--plan` and `--tag`;
nothing in the generators depends on the plan beyond its file. `--expect-bound` (default 231) and
`--bits`/`--lam` (default: the plan's `B` and `P/Q`) are the only knobs of the arithmetic.

**Plan verification.** Nothing of the plan's potential is used. The generator decodes the packed tables
back, runs Bellman–Ford from zero on the canonical labels with the weight
`Q (120 s + max(L5 fw, L5 rv, ctx7, ctx8)) − P` on every transition not excluded by a plain key or an H8
cut, requires a potential (no negative cycle) whose range fits the plan's `B` bits, re-checks every
transition of every label below 9 against the decoded tables while picking its witness code, and requires
`(P + 4200 Q) m ≤ 1099800 Q + 7 P + 2^B − 1` to give 231. Any failure exits with `PLAN REJECTED`. It also
asserts: keys are canonical RGS of the right lengths; 5-window fields with basis `lean_floor` satisfy
`level ≤ floorLevel`; `free233` 5-window fields have a 233 share key at ≥ the level (that key, with its
233 cap, is the Lean key, so the 233 certificate is reused verbatim); ctx and paid fields are not free.

## The chain (tag `L15268Q27`)

The plan (`milestones/28-combined-identities/data/certplan231_15268_27_dual.json.gz`, sha256 `a5d42188…`),
as the generator read and verified it (7 s; summary `data/auto6sc_L15268Q27.json`):

| item | value |
|---|---|
| λ_t, bits | P/Q = 15268/27, B = 15. Bellman–Ford from zero: 61 rounds, **range 26,450** (the plan says 26,450), so it fits 15 bits |
| bound | `(15268 + 4200·27) m ≤ 1099800·27 + 7·15268 + 32767 = 29834243`, so **m ≤ 231** |
| plain k6 keys | 45,181: 16,113 with a certificate already (5,347 keys of the 233 chain, 1,383 of the 235–237 replays, 9,383 by L1/L2 from a 233 seed) and **29,068 new**. 36 window shapes, 205 exclusion rows, 110 chunks of ≤ 400 keys in 7 key part modules |
| H8 keys | 262, the 233 chain's (not in the plan format; see "Problems found") |
| 5-window share fields | 25,058 in 51 rows on 9 shapes, 9-bit fields (max level 301): 23,054 on main's floors, **2,004 share keys** (1,940 new, 64 the 233 chain's own keys and caps), 47 chunks (one per shape and first count) |
| ctx 7 | **4,081 keys**, 138 nonzero rows on 34 shapes, 138 chunks (≤ 237 keys) |
| ctx 8 | **321 keys**, 87 nonzero rows on 43 shapes, 87 chunks (≤ 25 keys) |
| ctx fields | 8 bits (max level 200) |
| re-check | 10,404,288 transitions (34 shapes × every label below 9 × 6^6 counts); 2,892,199 allowed canonical transitions in the Bellman–Ford |
| witness codes | 0 (5-window forward): 4,949,771; 12 (reversed): 409,025; **13 (ctx 7): 12,558; 14 (ctx 8): 444**; 1–10 (k6 windows): 5,032,302; 11 (H8): 188. A code is the first one that works in the order 0, 12, 13, 14, exclusions |

The modules (identifiers carry the tag `L15268Q27`; `…` = `L15268Q27`):

| module | side | contents |
|---|---|---|
| `LocalWindowDirKeys6SC…P0` … `P6` | core | the 110 plain key chunks |
| `LocalWindowDirKeys6SC…` | core | `dirChunks6S…`, `h8Keys6S…`, `shareChunks6S…`/`shareKeys6S…`, `ctx7Chunks6SC…`, `ctx8Chunks6SC…`; `AllRefuted6S…`, `AllRefutedShare6S…`, `AllRefutedCtx6SC… := AllP RefutedCtx7 ctx7Keys6SC… ∧ AllP RefutedCtx8 ctx8Keys6SC…` |
| `WindowAutomaton6SC…Data` | core | `tables6SC…` (k6 masks, 15-bit potential rows, H8 tree, 9-bit share rows, 8-bit ctx 7 and ctx 8 rows) |
| `WindowAutomaton6SC…Shard<i>_<t0>` (204) | core | one `decide +kernel` of `check6SCAtW` per label, witness literals `nat_lit 0x…` |
| `WindowAutomaton6SC…Sequence` | core | `stepOK6SC… : StepOK6SC tables6SC…` |
| `DirectionWindowBridge6SC…R0` … `R5` | core | `keysOK6` of the key chunks, `rowOK6` of the 205 exclusion rows |
| `DirectionWindowBridge6SC…S` | core | `keysOKH8`, `CoverH8`, `ShareCover` by `shareCover_chunks` (54 row declarations) |
| `DirectionWindowBridge6SC…C` | core | `ctxCover7_6SC…`, `ctxCover8_6SC…` by `ctxCover_chunks` (2 zero checks, 462 row declarations) |
| `DirectionWindowBridge6SC…` | core | `Cover6`, `keysOK6`, `windows6SC…` |
| `AggregateDirection6SC…` | mathlib | `upper_231_of_refuted6SC…` (by `upper_of_refuted6SC`) |
| `Audit6SC…` | mathlib | `#check` and `#print axioms` |

All of the kernel checks print `propext`, `Classical.choice`, `Quot.sound` (or a subset): `stepOK6SC…`,
`windows6SC…`, `cover6S…k6`, `coverH8_6S…`, `shareCover6S…`, `ctxCover7_6SC…`, `ctxCover8_6SC…`.

## Measurements

Scratch build, `nice -n 10`, at most 2 of these `lean` processes at a time, next to 3 Python cost
computations and another agent's `lean` jobs on 4 cores (so wall time is 1 to 2.5 times CPU time).
CPU seconds and peak RSS are those of the `lean` process (`wait4`); for the rows marked † (first build)
the figure includes the `lake env` wrapper, about 0.45 GB, and no CPU time was recorded.
Log: `build231.py` jsonl files in the scratch directory.

| module | wall s | CPU s | peak RSS GB | `.olean` MB | source MB |
|---|---|---|---|---|---|
| `LocalWindowDirKeys6SC…P0` … `P6` † | 34–72 each, 336 in all | | 1.45–1.83 | 6.56 in all | 2.11 in all |
| `LocalWindowDirKeys6SC…` | 81.7 | 35.6 | 1.19 | 1.35 | 0.37 |
| `WindowAutomaton6SC…Data` | 67.1 | 26.1 | 0.36 | 4.67 | 4.86 |
| shards (204) | | **10.1–18.0 each, 3,086 in all (0.86 CPU-hours)** | 0.53–0.64 | 13.6 in all | 11.1 in all |
| `WindowAutomaton6SC…Sequence` | 36.2 | 35.0 | 1.34 | 0.79 | 0.04 |
| `DirectionWindowBridge6SC…R0` … `R5` | 4.5–26.2 | 77.7 in all | 0.46–0.53 | 0.54 in all | 0.05 in all |
| `DirectionWindowBridge6SC…S` | 147.0 | 125.9 | 2.90 | 0.27 | 0.02 |
| `DirectionWindowBridge6SC…C` | 2,469.9 | **1,973.5** | **4.60** | 1.34 | 0.17 |
| `DirectionWindowBridge6SC…` | 17.1 | 11.4 | 1.48 | 0.30 | 0.02 |
| `AggregateDirection6SC…` | 5.0 | 2.9 | 2.65 | 0.07 | |
| framework (`LocalWindowShareCtx`, `WindowAutomaton6SCDefs`, `…V2`, `DirectionWindowBridge6SC`, `…Chunks`, `AggregateDirection6SCConditional`) † | 1.5–7.5 each | | ≤ 3.08 | 2.3 in all | |

- The whole chain is about 1.5 CPU-hours: 0.86 for the shards (233: 0.69), 0.55 for the ctx cover, the
  rest under 0.1. The build directory holds 122 MB (sources, `.olean` files and the test certificates).
- Shards: 1 s of import plus about 1.5 s per induced label, as in 233; the ctx rows add only two
  `let`-bound 62 kbit rows per label. Each shard prints `propext`, `Quot.sound` through `stepOK6SC…`.
- The ctx cover is the dominant non-shard cost: 462 row declarations of 7,776 fields each, about 4 CPU-s
  each. `gen_lean_chain6sc.py --ctx-shapes-per-part K` puts the row declarations into part modules of K
  shapes, so that they build in parallel (the split form was generated but not built).

## Certificate driver `certify/cert231.py`

`cert231.py` reads the plan and pays only its rows with `free = false`:

| kind | plan rows | module pair | code path |
|---|---|---|---|
| `ctx` | 4,081 c7 + 321 c8 | `LocalWindowCtxCnf.C<ctx><dirs>A<t>K<cap>` / `LocalWindowCtxUnsat.C…` | core: `ctxcert.TaggedShareCtx` (`core_ctx`, which also records the full-proof LRAT size); Cnf: `ctxcert.emit_cnf` (= `cert233.emit_share` + the asserted rewrite to `checkAllSC`/`soundSC`); replay: cert233's replay loop (8 seeds × 5 rounds from 5 M estimated hints, else 2 × 1), checker v3 (`--seg 60000 --warm 32`), the import rewritten to `LocalWindowCtxCnf` |
| `share` | 1,940 new 5-window keys | `LocalWindowCnf.T…` / `LocalWindowUnsat.T…` | `cert233.core_share`, `cert233.emit_share`, the same replay loop; a key whose replay `.olean` exists (a 233 certificate) is skipped (none of the 1,940 is) |
| `seed` | 29,068 new plain keys | `LocalWindowCnf.S…` / `LocalWindowUnsat.S…` | `cert233.core_plain`; `plan` = cert233's seed plan (families L1/L2) over these keys only; Cnf `gen_lean_cnfsat_packed.emit --sat-v2` with the seed's widened bounds; the same replay loop |

Steps `keys`, `cores`, `plan`, `cnf`, `replay`, `build` (through `build231.py`), `publish`, `status`, all
resumable (an item whose output exists is skipped). `--index I --workers W` takes the items with
sha1(module name) mod W = I. `publish` pushes both sources of a certificate to `refs/heads/xfer/231/<name>`
(one orphan commit, gzip -9 parts under 45 MiB and `record.json` with sizes and sha256), with
`xfer233.push_blobs`; it was only run with `--dry-run`. Records go to `certify/data/<step>231_<plan>.jsonl`:
cores (core clauses, variables, `est_hints` = hints of the full proof, the plan's `plan_est_hints`,
seconds), cnf (source bytes, parts), replay (est_hints, core LRAT hints, lemmas, segments, `lean_bytes`,
LRAT seconds, producer), build (wall s, CPU s, peak RSS, `.olean` bytes).

**Five ctx certificates end to end** (plan `certplan231_15268_27_dual`; `CERT231_SCR` in the scratch
directory; one `lean` job, `nice -n 10`; core JSONs in `certify/cores/`):

| certificate | plan est. hints | full-proof hints | replay hints | core clauses | Cnf module: s / GB / `.olean` | replay module: s / GB / `.olean` | ms per hint |
|---|---|---|---|---|---|---|---|
| `C70123412A365354K11` (ctx 7, cap 11) | 8,111 | 4,228 | 2,177 | 955 | 6.6 / 0.85 / 0.10 MB | 0.7 / 0.47 / 0.04 MB | |
| `C801234523A652633K78` (ctx 8, cap 78) | 76,282 | 54,275 | 31,928 | 2,548 | 22.6 / 1.58 / 0.20 MB | 4.7 / 0.87 / 0.10 MB | 0.15 |
| `C70123425A656534K23` (ctx 7, cap 23) | 532,341 | 789,594 | 280,476 | 9,381 | 37.1 / 1.67 / 0.28 MB | 48.9 / 1.64 / 0.81 MB | 0.17 |
| `C70123412A632634K91` (ctx 7, cap 91) | 2,415,855 | 5,013,713 | 2,160,950 | 18,924 | 130.2 / 1.53 / 0.78 MB | 447.1 / 2.62 / 6.94 MB | 0.21 |
__BIG__

(CPU seconds of the `lean` process.) Generation (core, Cnf source, LRAT and v3 source) took 0.8 to 74 s for
the cores and up to 2,120 s of LRAT search for the largest (8 seeds × 5 rounds, one CaDiCaL job). Replay
sources: 16.6 kB to 48.8 MB (4.2 to 7.6 B per hint); replay `.olean` 3.2 B per hint for the 2 M one.
The glue test `CtxGlueTest231` (`TagsSW.refutedShareFrom_of_sat <name>.sat <name>.unsat`) states each
certificate as `RefutedCtx7 (dirs, t, level − 1)` / `RefutedCtx8 (…)` of its plan row: __GLUE__

## What is still missing for the unconditional 231

1. **The certificates.** Paid rows of this plan: 4,402 ctx (32.6 G hints by the plan's model),
   1,940 new 5-window share keys (17.3 G) and 29,068 new plain keys (38.5 G, before the seed plan
   removes the family-derived ones). The model is the plan's; the five measured ctx replays came out at
   0.27 to 0.94 of it. At the measured 0.15 to 0.21 ms per hint this is thousands of kernel-hours (233:
   3.34 G hints, 210 kernel-hours), so the plan's cost, not the Lean side, decides whether this plan is
   the one to certify. Driver: `certify/cert231.py`; nothing of production was started.
2. **Glue modules**, analogous to milestone 33's (not written):
   - `LocalWindowDirUnsat6S…` : `AllRefuted6S…`, from three sources: the 233 chain's `allRefuted6SB233`
     (its 6,794 plain and 262 H8 keys, which include the plan's 5,347 `reuse233` and 1,383 `reuse` keys),
     the 9,383 `derive233` keys by L1/L2 terms from the 233 seeds (`LocalWindowFamilies`, as
     `cert233.proof_term`), and the new seeds with their families; one kernel `mergeOK` per chunk of
     `dirChunks6S…` (as `cert233.py final`);
   - `LocalWindowShareUnsat6S…` : `AllRefutedShare6S…` (`AllRefutedShareList shareChunks6S….flatten`):
     the 64 reused 233 keys from `allRefutedShare6SB233`, the 1,940 new ones from
     `Tags.refutedShare_of_sat`, in chunk modules;
   - `LocalWindowCtxUnsat6SC…_<c>` and `LocalWindowCtxUnsat6SC…` : `AllRefutedCtx6SC…`, one
     `TagsSW.refutedShareFrom_of_sat` term per key (`CtxGlueTest231` shows the term for 5 keys), in chunks
     of 50 to 400; `ctx7Keys6SC…` is `ctx7Chunks6SC….flatten`, so the aggregate also needs
     `AllP P l.flatten` from `AllP P` of each chunk (a three-line lemma, not written).
3. **`UpperBound231.lean`**: `upper_231_of_refuted6SC… allRefuted… allRefutedShare… allRefutedCtx…
   Floors233Port.floors233`, then `chain_audit.py` and the `sorry`/`native_decide`/`axiom` grep, as in
   milestone 33. The generated core modules would first have to be placed in `work/final_lean` and built
   by `guarded_lake_build.py` (as the B233 data and shards were, with an old mtime and the sha256 file
   `data/shards6sc_L15268Q27.sha256`), or the audit run on the scratch directory.
4. Memory of the final import: 233's `UpperBound233` peaked at 12.61 GB under the 13.35 GiB limit. This
   chain adds about 36,000 more certificates, so the glue must be split finer than in 233, and that
   peak is the main risk of the last step.

## Problems found

- **Cover cost was quadratic (fixed with a new framework module).** `shareCover_rows` checks each
  share row against the whole key list (`keyLevel` scans it). With 2,004 share keys, one row declaration
  (193 key fields) went past 7 GB in a minute, and the first share module was killed at the 6 GB cap.
  `work/spectral/stronger/DirectionWindowBridge6SCChunks.lean` (new, 90 lines; standard axioms) proves
  `keyLevel_mono`, `shareRowOK_mono` and `shareCover_chunks`: each row (shape, first count) is checked
  against its own chunk of the keys, and `ShareCover T chunks.flatten` follows. `ctxCover_chunks` does the
  same for `CtxCover` with a chunk per shape and first count (`ctxCover_rows` had a chunk per shape).
  The share module then took 126 CPU-s and 2.9 GB. This is the only new proof; DESIGN.md said none would
  be needed.
- **The plan does not list the H8 keys.** `certplan231.World231` adds the 262 H8 cuts of the 233 chain as
  free and never drops them, and `rows()` skips them, so the generator reads them from
  `milestones/31-233-cost/data/keys233_best.json.gz`. If a later plan drops or adds H8 cuts, the plan must
  carry them: the generator reads a top-level `h8` list (`[[dirs8, syms6], …]`, the 233 key form) when
  there is one. **Request to the plan's author:** emit that list.
- **5-window levels above 255.** The largest 5-window level is 301, so those fields are 9 bits. The 6S
  share table takes any width, so nothing changed; ctx levels are at most 200 (8 bits).
- **A plan cannot be thinned by hand.** Dropping the 321 ctx 8 rows from this plan makes Bellman–Ford
  find a negative cycle (`PLAN REJECTED` after 5,000 rounds), although code 14 is the chosen witness of
  only 444 transitions: a ctx-7-only chain needs its own plan from `certplan231.py` (`NO_C8=1`).
- **`free233` 5-window rows.** For these 64 rows the Lean key is the 233 key with its own cap
  (T233 − 1 ≥ level − 1), so the 233 certificate is reused as it is; the generator asserts that such a key
  exists for each row.
- The plan's model hints were above the measured replay hints for the five ctx certificates (ratio 0.27 to
  0.94), and the full-proof estimate (`est_hints`) was 1.7 to 2.8 times the replay.

## Claims not verified by building

- The production of the certificates, the glue modules and `UpperBound231` (none exists).
- The `share` and `seed` paths of `cert231.py`: they call the cert233 functions that produced the 233
  certificates, but no 231 share or plain certificate was generated with them, and `cert231.py plan`
  (the seed plan) was not run, since it needs the cores of all 29,068 new plain keys.
- `cert231.py publish` without `--dry-run` (no branch was pushed), and multi-machine runs of
  `--index/--workers` (only the partition itself was checked).
- `--ctx-shapes-per-part`: generated, not built.
- The extrapolations in "What is still missing" (kernel-hours, glue memory).
- That the generated modules build in `work/final_lean` with `guarded_lake_build.py`: they were built
  only in the scratch directory.
