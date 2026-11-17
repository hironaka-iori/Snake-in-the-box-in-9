# Split certificates: `T012301A36264K45` (milestone 36)

Run of 17 November 2026 (branch `research/unconditional-241`). One paid certificate of the 231 plan
(`certplan231_563_1_cap`, share key `[[0,1,2,3,0,1],[3,6,2,6,4]]`, level 46, plan estimate 1.47 M hints) was far
larger than its plan estimate and did not finish on a 15 GB helper (8 h in the replay step at ~19 % CPU).

## Why it was slow

`cert231.replay` treats an item of at least 5 M estimated hints as *big*: 7 CaDiCaL configurations x 8 seeds
(21 runs per round) and up to 5 core-shrinking rounds. `--seed-jobs auto` admits parallel runs by 70 B per
estimated hint and run; at 167.7 M full-proof hints that is 11.7 GB, so the runs go one at a time (one of four
cores, the observed duty). After the search, `gen_lean_lrat_v3.py` holds every hint as a Python object: here it
was OOM-killed at 12.8 GB. A single merged module would have needed an estimated ~10 CPU-hours of kernel time
in one process.

## Size

| | |
|---|---|
| core | 30,336 clauses, 11,231 variables (cores step 728 s; full-proof estimate 167,738,449 hints) |
| core LRAT | 92,617,148 hints, 1,244,247 lemmas: `cadical --lrat --no-binary --seed=1 --unsat --subsume=0`, one round, 294 s (3 configurations in parallel) |
| Lean source | 1,545 segments, 481 MB (`--pack-chunk 2048`), generated in 192 s at < 0.4 GB |

## Route: a module split, no new lemmas

`LratV3.check OFF W M FLAG raw Ps T c` reads `Ps` only through `segP`. So the generator's declarations can be
distributed over modules unchanged:

| module | contents | build (this certificate) |
|---|---|---|
| `LocalWindowCertSplit.N.Cnf` | the Cnf body (`raw`, `cnf`, tags, `check_*`, `sat`), public and exposed | 62 s, 0.83 GB |
| `LocalWindowCertSplit.N.D0`..`D11` | the segment data `p<c>`, `t<c>` (40 MB of source each), public and exposed | 24 s, 0.22 GB each |
| `LocalWindowCertSplit.N.Ps` | `Ps := [p0, …, p1544]` | 0.6 s |
| `LocalWindowCertSplit.N.K0`..`K15` | `ok<c>` (and `warm<c>`) of ~97 contiguous segments each, `by decide +kernel`, generator text | see below |
| `LocalWindowCert.N` | private imports of Cnf, Ps and every K; the generator's `steps*` and `unsat`; `public theorem refuted : RefutedShare (winOf [0, 1, 2, 3, 0, 1]) (boundsOf [3, 6, 2, 6, 4]) 12 45` | seconds |

The K parts depend only on Cnf, D and Ps, not on each other, so they are built on different machines. The final
module only type-checks the `seg_step` chain. Its exported imports are `{LocalWindowShareCtx}`, as for a merged
certificate, and it exports only `refuted`, so glue, `assemble435.py` and `audit.py` load only its public
`.olean`: the parts are never opened downstream.

**Consistency of the parts.** A part `.olean` states `ok<c>` about the constants `Ps`, `t<c>`, `raw` of the
Cnf/D/Ps modules. The final machine accepts a part only if the part's manifest gives, for each of those
modules, the same source sha256 and the same `.olean` sha256 as its own build (4.35 output is byte-
deterministic; this held across three working directories in the toy test and across machines here).

## Tools (`lean435/tools`)

| tool | what it does |
|---|---|
| `bigreplay435.py` | the share replay step with the portfolio, rounds and generator options exposed; keeps the LRAT |
| `genv3stream.py` | low-memory twin of `gen_lean_lrat_v3.py`; three passes over the LRAT, segment by segment. **Byte-identical output**, tested on `T012345A34466K23` with pack chunks 16384 and 2048 |
| `split435.py` | writes the modules above from the generator output (the same inputs as `to435.py`) and `SPLIT-MANIFEST.N.json` (sha256 of every source) |
| `splitfarm435.py` | `prepare` (cores, cnf, `bigreplay435`, `split435`, `pack`: the generation of one certificate), `pack` (gzip sources to `xfer/c435split/src-N`), `part --k K…` (fetch, check, build base and parts, push to `xfer/c435split/N-k<K>`), `final` (fetch and check every part, build the final module, write the prod435 record, publish to `xfer/c435help/w<J>`) |

## Validation on a small certificate (`T012345A34466K23`, 3.22 M hints, 55 segments)

- Merged module (`to435.py`): 513 CPU-s, 2.13 GB.
- Split into 3 parts: Cnf 30 s, 4 data modules 7.5 s each, parts 143 / 156 / 173 s at 1.6-2.1 GB, final 0.4 s.
  Same `refuted` statement text.
- Interface-only audit (`audit.py final --olean-only`) of a module importing the split certificate: 16 import
  artifacts, only `T012345A34466K23.olean` of ours opened, `[propext, Classical.choice, Quot.sound]`:
  AUDIT PASSED.
- Farm flow against a local bare remote: two parts in two working directories, the final in a third (base
  `.olean` hashes matched), publication to `c435help/w150`, `prod435.py status` lists it.

**Part memory does not shrink with the part.** Peak memory is per declaration (kernel caches are per
declaration) and grows with how far a segment's hints reach back (decoded segments of `Ps`). The toy's last
third peaked at 2.06 GB against 2.13 GB for the whole. Smaller ProofPack chunks (2048 instead of 16384 bytes)
cut the toy part's peak from 2.06 to 1.67 GB and its time by ~10 %. Probes of this certificate (two segments
each): 2.06 GB (segments 100-101), 4.26 GB (1100-1101), 3.60 GB (1543-1544), 0.2-0.4 ms per hint.

## Results (published to `refs/heads/xfer/c435help/w150`)

All five were used by the final 231 audit (`Snake9.upper_231_435`, commit `de6a9ad3`). Full records (the prod435
manifest line with its `split` field: source and part sha256, CPU s and peak of every module; and the
`SPLIT-MANIFEST` with the sha256 of every source) are in [`split231/records.json.gz`](split231/records.json.gz).

| certificate | plan est | full-proof est (cores) | core LRAT hints | segments | parts | longest part (s) | lean CPU in all | peak RssAnon | sources pushed -> published (UTC) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `T012301A36264K45` | 1.47 M | 167.7 M | 92,617,148 | 1,545 | 16 | 4,412 | 44,854 s | 5.60 GB | 17:58 -> 19:22 |
| `T012301A46246K33` | 1.45 M | 83.1 M | 47,597,174 | 794 | 8 | 2,966 | 19,580 s | 3.98 GB | 18:11 -> 19:17 |
| `T012301A33436K47` | 32.0 M | 68.0 M | 44,154,462 | 739 | 8 | 2,320 | 15,274 s | 4.38 GB | 19:04 -> 19:52 |
| `T012301A35353K20` | 0.53 M | 116.9 M | 65,898,672 | 1,102 | 16 | 2,732 | 30,636 s | 5.98 GB | 19:48 -> 20:41 |
| `T012301A26346K35` | 2.32 M | 147.6 M | 78,758,795 | 1,315 | 16 | 2,260 | 26,975 s | 5.18 GB | 20:57 -> 21:38 |

| certificate | statement of `refuted` | public `.olean` sha256 | bytes |
|---|---|---|---:|
| `LocalWindowCert.T012301A36264K45` | `RefutedShare (winOf [0, 1, 2, 3, 0, 1]) (boundsOf [3, 6, 2, 6, 4]) 12 45` | `2b46265af9cdf5b5f7802d6f7abfdec596404ca65690066d38fbf305951af126` | 8,664 |
| `LocalWindowCert.T012301A46246K33` | `RefutedShare (winOf [0, 1, 2, 3, 0, 1]) (boundsOf [4, 6, 2, 4, 6]) 12 33` | `af4922f31f0c99be1c5f7db36a892d8a8ae6e6e0ea97acce2873460b5fed2a47` | 7,832 |
| `LocalWindowCert.T012301A33436K47` | `RefutedShare (winOf [0, 1, 2, 3, 0, 1]) (boundsOf [3, 3, 4, 3, 6]) 12 47` | `249d7c184c900e8b3fc003f4faf9b163c5d95a721f6772b60fb8e527b09d784b` | 7,832 |
| `LocalWindowCert.T012301A35353K20` | `RefutedShare (winOf [0, 1, 2, 3, 0, 1]) (boundsOf [3, 5, 3, 5, 3]) 12 20` | `2fc0915b7d8e9994fef52dffd563ba1c77096722a30816ed392a21b52137dd7a` | 8,496 |
| `LocalWindowCert.T012301A26346K35` | `RefutedShare (winOf [0, 1, 2, 3, 0, 1]) (boundsOf [2, 6, 3, 4, 6]) 12 35` | `8b24f3e14b3398519ca6a041292b3a26b42d93d9046976e0b484dd002e2592ea` | 8,664 |

- Generation (cores, cnf, LRAT, Lean source, split) took 15-25 min per certificate on one 4-core machine.
- The statements are what `to435.py` writes for the same generator output (checked by diff for K45; all use
  `port.refuted_decl`).
- Parts ran two per machine on 15 GB machines (cap 7 GB each), on 4-7 farm machines per certificate plus this one.
  Every part's base modules (Cnf, D*, Ps) had the same `.olean` sha256 as the final machine's.
- Interface-only audit of each published `.olean` (`audit.py final --olean-only`, a module importing the
  certificate and printing its axioms): only that `.olean` of ours opened, `[propext, Classical.choice,
  Quot.sound]`, AUDIT PASSED.
- `splitfarm435.py final` refuses to publish a module that any owner or helper branch already has. It was added
  after `T012304A44356K33` had been published by the stock route while its split parts were running; those were
  stopped, and nothing of it was published on w150 (its part refs `xfer/c435split/T012304A44356K33-k0/k1` and
  `src-…` exist but are not used by anything).
- A stock duplicate of one of these modules published later would have a different `.olean` (another proof):
  `prod435.py merge` would report a CONFLICT; both would be valid certificates of the same statement.

## How to reproduce one split certificate

On a 15 GB, 4-core machine with this branch checked out (Lean 4.35 at `/opt/lean-4.35.0-linux`, CaDiCaL 2.1.3):

```bash
python3 lean435/tools/prod435.py setup                       # core stack, ~2 min
P=milestones/28-combined-identities/data/certplan231_563_1_cap.json.gz
# 1. from scratch: generation, split and source push (15-25 min). To re-check a published certificate,
#    skip this step: its sources are on xfer/c435split/src-N and `part`/`final` fetch them.
python3 lean435/tools/splitfarm435.py prepare --plan $P --name N --parts 16
# 2. on each part machine (two parts at a time, 7 GB cap each), K = 0..15:
python3 lean435/tools/splitfarm435.py part --name N --k K --k K+1
# 3. on the final machine (re-checks base hashes of every part, builds the final module, publishes to w<J>):
python3 lean435/tools/splitfarm435.py final --name N --plan $P --index J --require-remote [--no-publish]
```

`prepare` produces a new proof whenever CaDiCaL or the generator change, so its sources need not match the
published ones byte for byte; with the same CaDiCaL binary they did in our runs (the toy items were regenerated
with identical output). `final --no-publish` writes `split/N/job/result.json` and the final `.olean` only. Every
part can be built on one machine too (`part --k 0 --k 1`, then `--k 2 --k 3`, …); only wall time changes.

## What an independent re-check needs (refs to keep)

| ref | contents | needed for |
|---|---|---|
| `refs/heads/xfer/c435split/src-N` | gzip sources of every module of the split and `SPLIT-MANIFEST.N.json` | re-running every kernel check from source (`part`, `final`) |
| `refs/heads/xfer/c435split/N-k<K>` (8 or 16 per certificate) | part `.olean` files and their build manifests | rebuilding the final module without re-running the parts (the provenance of the published `.olean`) |
| `refs/heads/xfer/c435help/w150` | the five published public `.olean`, `manifest.jsonl` | the 231 glue and audit |

For N in `T012301A36264K45`, `T012301A46246K33`, `T012301A33436K47`, `T012301A35353K20`, `T012301A26346K35`. A full
re-check from source needs only `src-N` (and this branch): `part` for every K, then `final --no-publish`, and a
comparison of the new final `.olean` sha256 with w150 (4.35 builds are byte-deterministic, so it should be
equal). The part refs are not needed for that, but they are the record of what was checked where; keep them.
Not needed: `xfer/c435split/src-T012304A44356K33` and its `-k0`, `-k1` refs.

## Lessons for future plans

- **The plan estimates of unmeasured share items were far off.** Real core proofs against plan estimates:
  63x (K45: 92.6 M vs 1.47 M), 33x (K33), 124x (K20: 65.9 M vs 0.53 M), 34x (K35); the cores step's full-proof
  estimates were 34x-219x the plan. Only the cores estimate (x ~0.55 for the core proof) is usable for
  scheduling; run the cores step of every item early and re-plan on it.
- **The stock replay search is the wrong default above ~5 M estimated hints.** 7 configurations x up to 8 seeds
  (21 runs) x up to 5 shrinking rounds, admitted one at a time under the 70 B/hint memory gate, kept one core busy
  for 5-9+ h per item here. The portfolio changes the hint count by up to ~25 % and shrinking rounds sometimes
  more, but parallel parts make kernel time cheap, and the search itself costs more than it saves. Recommended:
  `bigreplay435.py` defaults (3 configurations in parallel: `--unsat`, `--unsat --subsume=0`, default; one round;
  ~3-5 min at 50-90 M hints).
- **The stock generator (`gen_lean_lrat_v3.py`) runs out of memory near 90 M hints** on 15 GB (12.8 GB killed
  at 92.6 M; 13.5 GB on helper 106). `genv3stream.py` gives the same bytes in < 0.4 GB; use it always.
- **Above ~20 M core-proof hints, split.** A single module of 50-70 M hints takes 6-10 h of kernel time in one
  process at 9-10 GB; split into parts of ~3-6 M hints (8-16 parts), peak 2-6 GB per part, 15-75 min each.
  Smaller ProofPack chunks (`--pack-chunk 2048`) lower the per-declaration peak (and time ~10 %).
- **Peak memory is per declaration** and grows with how far a segment's hints reach back; a module split does not
  lower it, only the proof does. Probe the last segments (a module with their `ok` theorems only) before choosing
  caps.
- **Check publication right before publishing** a certificate that may also be running elsewhere.
