# Sampling rebuild of the 231 certificates (18 November 2026)

The kernel checks of the 24,797 certificates behind `Snake9.upper_231_435` are single runs on the farm
machines; the audit consumed only their public `.olean` files (see the 231 caveats in
[`../../README.md`](../../README.md)). As evidence for reviewers, a seeded random sample of them was
rebuilt from the committed plans with the same toolchain. Each rebuild ran the Lean kernel again on the
certificate's proof. Its outputs were then compared byte for byte with the manifest the 231 audit used.

## Result

**275 of 275 sampled certificates rebuilt to the same public `.olean` (sha256) as in
`../manifest231.jsonl.gz`.**

- Every regenerated Lean source has the manifest's source sha256.
- So do the other four build outputs (`.olean.server`, `.olean.private`, `.ir`, `.ir.sig`).
- The rebuilt proofs have exactly the recorded number of replay hints.
- No mismatch, and no error that would count against reproduction (see "Incidents" below).

| stratum (hints decile) | sampled | hints range | MATCH |
|---:|---:|---|---:|
| 0 | 30 | 13 - 7,894 | 30 |
| 1 | 30 | 9,022 - 27,362 | 30 |
| 2 | 30 | 31,752 - 79,955 | 30 |
| 3 | 30 | 84,717 - 172,392 | 30 |
| 4 | 30 | 177,400 - 249,877 | 30 |
| 5 | 30 | 278,507 - 449,362 | 30 |
| 6 | 30 | 453,643 - 860,395 | 30 |
| 7 | 30 | 873,812 - 1,887,793 | 30 |
| 8 | 25 | 1,984,892 - 4,480,355 | 25 |
| 9 | 10 | 5,054,625 - 19,241,602 | 10 |

Totals: 275 certificates, 249.5 M replay hints, 14.2 Lean CPU-hours of kernel checking (farm: 12.8), 275 MATCH, 0 MISMATCH, 0 ERROR; source sha256 equal for 275, all five parts equal for 275, rebuilt hints equal for 275.

## Population, sampling, seed

- **Population:** the 24,797 lines of `../manifest231.jsonl.gz` (gzip sha256
  `ea21bc2d543f4b8b273cd11f5e9ceaa3e1d1d4418122658bcebeb92e783e7398`), i.e. every certificate module the
  231 glue imports.
- **Strata:** the 10 equal-count deciles of the recorded replay `hints`, sorted by (hints, module).
- **Per-stratum counts:** 30 each in deciles 0-7, 25 in decile 8 and 10 in decile 9, for 275 in total.
- **Exclusions:**
  - The 5 split certificates of SPLIT.md were left out. Their kernel checks live in part modules built
    on several machines, so the monolithic rebuild path does not apply to them.
  - In decile 9, only items of at most 20 M hints were drawn, so that one build stays under about 3 h.
    The 231 top decile runs to 92.6 M hints. The largest item rebuilt here has 19.2 M hints.
- **Drawing:** `random.Random(f'{seed}-{d}').sample(stratum_d sorted by module, k_d)` with seed
  `231-sample-20261118`.
- **Files:** the list is `sample.jsonl` (first line: the parameters; then one line per item, with the
  manifest's sha256 values). The rebuild results are `results.jsonl`.
- **Mix of the sample:**
  - kinds: 232 plain, 26 ctx and 17 share certificates;
  - plans: 156 from `certplan231_563_1_cap` (the 231 plan), 66 from `certplan231_m232_541_1b` (the 232
    plan, whose certificates the 231 glue reuses) and 53 from `freeplan_certplan231_m232_541_1b` (233-era
    free keys);
  - the farm generator commits of the sampled items span 10 different commits.

## Method

`rebuild231.py run` rebuilds each item with `lean435/tools/prod435.py one`, the same per-certificate
path the farm ran:

1. `cert231.py` (through `cert435.py`, unchanged) regenerates the CNF, the core and the CaDiCaL 2.1.3
   LRAT proof. The proof is chosen by the same search as on the farm, with `gen_lean_lrat_v3.py` as the
   generator.
2. `to435.py` writes the 4.35 module.
3. `build.py` compiles it with Lean 4.35.0 (`eb6cafb7`) against the locally built core stack (core
   manifest sha256 `2df1ab8d…`, the same as the farm's). This compile is the kernel check.

The plans are the committed files: `milestones/28-combined-identities/data/certplan231_*.json.gz`, and
`lean435/data/freeplan_*`/`freeseeds_*`. The paid plain keys use prod435's self-seed file, as on the
farm. The generators were today's (`rebuild_commit` in each row: 87fbd8e5). The farm builds used 10
earlier commits (`farm_generator_commit`). The identical outputs show that these commits generate the
same sources for these items.

Each row of `results.jsonl` holds:

- `result`: MATCH when the public `.olean` sha256 equals the manifest's;
- `source_match`, and `other_parts_match` per extension;
- `rebuilt_hints` against `hints`;
- the rebuild's Lean CPU time against the farm's, its peak RssAnon, host and time.

Reproduce with `python3 rebuild231.py sample` (writes the same `sample.jsonl`), then
`python3 rebuild231.py run --jobs 3` and `python3 rebuild231.py summary`. Run it in a checkout with
`prod435.py setup` done, without `PROD435_ADAPTER`/`PROD435_CERT` set.

Runtime: one 4-core, 15 GB machine, 11:33-20:12 UTC, beside other work. The largest items took 5.3 h
each, almost all of it in the stock 21-run CaDiCaL replay search, which the farm ran too.

## Incidents

To use idle cores, a second `rebuild231.py run` process was started on the small strata, smallest first
(`--smallest-first --strata`), beside the first. The first process predated the duplicate check added
for this. In decile 8 both processes built 3 items (`S0120314A465354`, `S0123024A454444`,
`S0123024A564346`) at the same time in the same job directory. Their LRAT files were corrupted (NUL
bytes, missing clause ids in `trim_lrat`), and those builds stopped with Python errors before any Lean
step. Those 5 ERROR rows are kept in `results-raw-incident.jsonl`. The 3 items were then rebuilt alone,
from clean job and core directories, and their rows in `results.jsonl` are those clean rebuilds.

## What this does and does not show

- **It shows:** for a seeded, size-stratified random sample of 275 certificates (1.1 %), an independent
  rebuild of the generation and the kernel check, on another machine and today, gives bit-identical
  certificates. A sampled certificate that was wrong on the farm, or whose `.olean` did not come from
  its recorded proof, would have shown as a MISMATCH here.
- **It does not show:** anything about the 24,522 certificates outside the sample. Under random
  sampling, 275 of 275 matching bounds the fraction of non-reproducible certificates below about 1.1 %
  at 95 % confidence (rule of three). It does not cover the 5 split certificates or items above 20 M
  hints.
- **Same kernel:** the rebuild uses the same Lean kernel (C++, 4.35.0) as the farm. It is a second run,
  not an independent kernel.
