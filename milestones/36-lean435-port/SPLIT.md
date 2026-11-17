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
| `splitfarm435.py` | `pack` (gzip sources to `xfer/c435split/src-N`), `part --k K…` (fetch, check, build base and parts, push to `xfer/c435split/N-k<K>`), `final` (fetch and check every part, build the final module, write the prod435 record, publish to `xfer/c435help/w<J>`) |

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
