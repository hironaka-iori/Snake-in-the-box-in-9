# Certificates of the unconditional 233

Driver for the two premises of
`Snake9.Floors233Port.upper_233_of_certs6SB233 (h : AllRefuted6SB233) (hs : AllRefutedShare6SB233) : m ≤ 233`
(`work/spectral/stronger/Floors233Main.lean`). It adapts the k7 pipeline of
`milestones/25-k7-234/certify` (`gen_k7_core.py`, `replay_k7.py`, `families_k7.py`) to the key lists of
`work/final_lean/LocalWindowDirKeys6SB233.lean`. The progress log of the production run is
[`../CERT-PROGRESS.md`](../CERT-PROGRESS.md).

| file | contents |
|---|---|
| `cert233.py` | `cores`, `plan`, `cnf`, `replay`, `final`, `status` (see its docstring) |
| `share233.py` | the share CNF with Lean meanings and tags: main's `tagged_share.py` (milestone 28 of main, blob `8a6f27d8`), on this branch's `TaggedEncoding`, plus lazy cycle cuts |
| `prod233.py` | production batches: generate, staleness simulation, guarded build, sweep of sources, under a disk reserve |
| `data/sample233.json` | the validation sample |
| `data/seeds6SB233.json.gz` | the seed plan (written by `cert233.py plan`) |
| `data/replay6SB233.jsonl`, `data/prod6SB233.jsonl` | per-certificate replay records and per-batch records |

Core JSONs (one gzipped file per key, the CNF regenerated from it and checked by SHA256):
`milestones/10-window-aggregate/data/lean_core_direction_6s/`.

## The three certificate kinds

| kind | count | module prefix | CNF | clause soundness | replay |
|---|---|---|---|---|---|
| plain k6 key, new | 5,411 | `S<ds>A<syms>` | `gen_k7_core.encoding` (radius 4) + lazy cycle cuts | Sat v2 (`gen_lean_cnfsat_packed.emit --sat-v2 --part-lits 4000`, `TagsW.checkAllT`), widened `bounds` for a seed | checker v3 (`LratV3`, seg 60k) |
| H8 key | 262 | `S<ds>A<syms>` | the same, the 8th interior vertex uncounted (as H9 in milestone 25) | the same | the same |
| share threshold | 490 | `T<ds>A<syms>K<K>` | `share233.TaggedShare` (cap `K`, resolution 12) + lazy cycle cuts; the core renumbered compactly | `emit_share`: `TagsSW.checkAllS` with flat tables (`TagsW.getF`, `TagsSW.getSF`), tags `Tags.tagsOfSL`, totalizers `Tags.natsOf`; counters, totalizers and clause parts checked separately (`TagsSW.checkAllS_of_parts`, `TagsSW.ckAllS_append`) | the same |
| plain key, reused | 1,383 | the old `Q`/`R`/`K` window modules | | `LocalWindowSat.W` | `LocalWindowUnsat.W` (being migrated to v3, same name and theorem) |

`share_compact` follows main's `prepare_lean.py` (milestone 73): the core's variables first, then the
other variables of the kept counters and of all totalizers. Soundness does not depend on any of this
packing: `TagsSW.soundS` holds for every table and tag list that `checkAllS` accepts, and `sat` and
`unsat` are both about the same `cnf`.

**Seeds and families.** The core of every new plain/H8 key is the first configuration (`--unsat`) of
`FULL_PORTFOLIO`; the counters it uses give the widened bounds (`families_k7.wide_bounds`). `plan` is
`families_k7.main` on these widened cores (weighted greedy cover, cost = full-proof hints + 5,000;
L1 and L2 checked by the exact mirrors). So a seed is certified with exactly the bounds its own core
allows, and no orphans arise. Share thresholds are not widened (no `RefutedShare` analogue of L1).

**Premise modules** (`final`, in `work/final_lean`):

- `LocalWindowDirKeysN6SB233`: the new keys, sorted, in chunks of 400 (plain, then H8);
- `LocalWindowDirUnsatN6SB233_<c>`: per key `S….refuted : Refuted (winOf ds) (boundsOf syms)` by its
  own certificate (narrowed by L1 for a widened seed), or by L1/L2 from its seed; `Elab.async false`;
- `LocalWindowDirKeysR6SB233`, `LocalWindowDirUnsatR6SB233`: the reused keys from their window modules;
- `LocalWindowDirUnsat6SB233`: `allRefuted6SB233 : AllRefuted6SB233`, one kernel `mergeOK` per chunk
  of `dirChunks6SB233` and one for `h8Keys6SB233`, against `dirKeysR6SB233 :: dirChunksN6SB233`;
- `LocalWindowShareUnsat6SB233_<c>` (50 keys each) and `LocalWindowShareUnsat6SB233`:
  `allRefutedShare6SB233 : AllRefutedShare6SB233`;
- `work/spectral/stronger/UpperBound233.lean`: `upper_bound_233`, `verified_interval_191_233`.

## Validation (10 November, scratch)

Sample `data/sample233.json`: 18 new plain keys of four windows, 2 H8 keys, 2 share thresholds (the
two cheapest), 5 reused keys (3 `Q`, 2 `K`). Cores, plan, Cnf, replays and `final --keys-from` were run
into a scratch root and every module compiled with one `lean -o` (`nice -n 10`), scratch `.olean`
first in `LEAN_PATH` (the reused `LocalWindowUnsat` windows symlinked into it, since a scratch
`LocalWindowUnsat/` directory hides the production one).

| step | result |
|---|---|
| cores | 22 cores in 9 s; the plan: 7 seeds (6 plain, 1 H8, all widened), 13 keys by L1 |
| Cnf, Sat v2 (7 seeds) | 0.3-1.4 s, at most 0.45 GB, 45-61 kB `.olean` each |
| Cnf, share (`T012034A32663K3`, 892 clauses; `T012340A42626K15`, 2,718 clauses) | 6.5 s / 0.75 GB / 96 kB; 16.9 s / 1.33 GB / 139 kB |
| replays, v3 (9) | 0.2-2.5 s, at most 0.62 GB; the share replays have 2,026 and 8,111 hints |
| chunks `LocalWindowDirUnsatN6SB233_0`, `_1` (18 + 2 keys, 7 own, 13 L1) | 0.3 s and 0.2 s, 0.41 GB |
| `LocalWindowDirUnsatR6SB233` (5 reused keys) | 0.2 s |
| mini premises `LocalWindowDirUnsat6SB233Mini` (merge of 23 plain and 2 H8 keys), `LocalWindowShareUnsat6SB233Mini` | 0.4 s, 0.3 s |

```
'Snake9.LocalWindow.allRefutedMini6SB233' depends on axioms: [propext, Classical.choice, Quot.sound]
'Snake9.LocalWindow.allRefutedShareMini6SB233' depends on axioms: [propext, Classical.choice, Quot.sound]
```

L2 (`refuted_key_sub`) did not occur in the sample; its term is the one validated in milestone 25
(`gen_k7_core.proof_term`).
