# The conditional 231 chain (context shares, milestone 35)

Run of 15 November 2026. The design and the generic Lean framework are in [DESIGN.md](DESIGN.md). This file
covers the generated part: the generators, the dry run and scratch build on the certificate plan of
`milestones/28-combined-identities/certplan231.py`, and the certificate driver.

**Status.** __STATUS__

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

__CHAIN__

## Measurements

__MEAS__

## Certificate driver `certify/cert231.py`

__CERT__

## What is still missing for the unconditional 231

__MISSING__

## Problems found

__PROBLEMS__

## Claims not verified by building

__CLAIMS__
