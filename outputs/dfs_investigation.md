# Exhaustive bitset DFS: deeper regrowth, combined moves, and rigidity

Date: 15 October 2026. Verified bounds remain 191 <= a(9) <= 245 (the Lean-checked upper bound on `main` at the time of this PR). No longer snake was found. Every exclusion below is an exhaustive computer search in a restricted family, and none bounds a(9). Only the parity restriction and the regrowth exclusions with 160 and 152 fixed vertices are Lean-certified (see Lean verification).

## Tool

`work/snake_dfs.c` is a standalone C program (no dependencies) that grows induced paths with 512-bit bitsets. It prunes with two upper bounds on the number of vertices an extension can still add from the head:

1. **Parity bound.** Count the free vertices reachable from the head. A path alternates between even and odd weight, so it can use at most `min(opp, same+1) + min(same, opp)` of them.
2. **Leaf-peeling bound.** In the reachable free region plus the head, repeatedly remove vertices of degree at most one. A removed tree hangs off the rest by at most one edge, so a path that enters it must end inside it. The extension therefore uses at most (core size) + (largest peeled-tree height) vertices.

Both bounds are valid for any induced path, and the second shrinks node counts by about 5x at Q9 depth. `work/dfs_driver.py` runs the program in parallel and re-checks every reported path with `check_snake.verify`, using all-pairs verification.

**Controls** (`work/dfs_controls.py` -> `dfs_controls.json`, all passed):
- exact maxima from vertex 0 in Q3, Q4, Q5 and Q6 (4, 7, 13 and 26 edges), each reached and each exceeded target excluded, with and without peeling;
- 600 outcome comparisons with an independent unpruned Python DFS on random Q4/Q5 prefixes;
- every bank snake regrows to 191 edges from its first 150 vertices.

The tool also found a 50-edge Q7 snake from scratch in 253 s. It cannot exhaust Q7 without symmetry breaking.

## Parity restriction on internal changes

Q9 is bipartite. Any replacement of the stretch between two retained path vertices a and b has length congruent to d(a,b) mod 2. Replacing an internal window alone therefore changes the length by an even amount: 191 can become 193, never 192. A 192-edge snake that shares an internal skeleton with a bank snake must differ at an end. That is why the searches below always free at least one end.

## Results

### 1. End regrowth (exhaustive, both ends of all 131 bank snakes)

The model fixes the first KEEP vertices, then searches all induced extensions for a 193-vertex (192-edge) snake.

| KEEP | Freed vertices | Outcome (262 runs) | Nodes | Wall time (12 workers) | Record |
|---:|---:|---|---:|---:|---|
| 128 | 64 | all INFEASIBLE | 3.5e7 | 3 s | `dfs_regrow_keep128.json` |
| 120 | 72 | all INFEASIBLE | 3.3e8 | 34 s | `dfs_regrow_keep120.json` |
| 112 | 80 | all INFEASIBLE | 5.4e9 | 810 s | `dfs_regrow_keep112.json` |
| 104 | 88 | running (cap 5e8 nodes per run; first results INFEASIBLE at 1.5-2.1e8 nodes) | | | `dfs_regrow_keep104.partial.jsonl` |

Rerunning the same `regrow` command resumes from the `.partial.jsonl` log. Earlier Python regrowth stopped at 40 freed vertices, and 53 of its 48-vertex instances were left unresolved. Each extra 8 freed vertices costs roughly 10-15x more nodes.

**Interpretation.** A 192-edge snake, if one exists, cannot share a 112-vertex end segment with any of the 131 published 191-edge snakes. Shorter shared segments are untested.

### 2. Rigidity of internal windows (exhaustive)

For random internal windows, the search deleted W consecutive vertices and enumerated every induced filling between the retained ends. It was run on the first six bank snakes with six windows each.

| W | Windows | Fillings per window | Longer (+2) fillings |
|---:|---:|---|---:|
| 20 | 10 (first two snakes, five each) | all 1 (the original) | 0 |
| 30 | 36 | 31 x 1, 5 x 2 | 0 |
| 40 | 36 | 30 x 1, 6 x 2 | 0 |
| 50 | 36 | 29 x 1, 7 x 2 | 0 |
| 60 | 36 | 29 x 1, 7 x 2 | 0 |
| 80 | 36 (34 exhausted) | 29 x 1, 7 x 2 | 0 |

Typically, an 80-vertex internal stretch, 42% of the snake, is determined uniquely by the rest. As a result, plateau random walks among 191-edge snakes have almost no room to move. Diversification has to come from changes at the ends or from new constructions, not from internal swaps.

### 3. Combined moves: truncate, shorten a window, regrow (random LNS)

Each job:
1. truncates a bank snake (random orientation) to CUT in [140, 180] vertices;
2. deletes a random internal window of 16-48 vertices;
3. enumerates every induced filling up to 2*SLACK edges shorter (SLACK 1 or 2);
4. regrows the end exhaustively for 193 vertices after each filling.

This targets the handoff's "replace internal portions and endpoints together". A shorter filling frees room near the end, so the end can gain 3 or 5.

The run covered 2105 jobs, 6315 windows and all 131 bank snakes, in 1525 s on 12 workers with seed 1.

| Statistic | Count |
|---|---:|
| Fillings tested, each followed by an exhaustive regrowth | 527,838,115 |
| Regrowths reaching the 200k node limit | 0 |
| Window enumerations reaching the 2e7 node limit | 1520 (those windows partially covered) |
| 192-edge snakes | 0 |

Record: `dfs_combo_s1.json`. This is a random sample of a huge move space, not an exhaustive result.

### 4. Q8 seeds: the known 98-edge snake is rigid

The search fixed the first KEEP vertices of the Carlson-Hougen 98-edge Q8 snake and enumerated every 98-edge completion, in both orientations.

| KEEP | Completions (forward, reverse) | Nodes |
|---:|---|---:|
| 70, 60, 50 | 1, 1 (the seed itself) | < 6e3 |
| 40 | 1, 1 | 7.9e7, 6.5e5 |
| 30 | PENDING | |

Even with 59 of its 99 vertices freed, the seed admits no other optimal completion. 98-edge Q8 snakes therefore appear sparse and isolated. "Diverse 98-edge seeds" cannot be produced by local modification of the known one; they need a global Q8 enumeration.

### 5. Exact partner length for the 98-edge seed

The single-crossing model was encoded as Q9 regrowth confined to the second layer: the seed in layer 0, a crossing at its endpoint, then free growth inside layer 1. Status: PENDING. With 157 free vertices, the reachability bounds are weak in this setting, and the 97-edge target did not resolve within 3e9 nodes.

## Lean verification

Three Lean modules in `work/final_lean/` connect these results to the project's `Snake9.Snake` definition. They use only the standard library, and their axiom audits list only `propext`, `Classical.choice` and `Quot.sound`. No `sorry` and no `native_decide` appear.

- **`DfsParity.lean`: the parity restriction above, proved.** `endpoint_parity`, `same_endpoints_same_parity` and `no_192_with_endpoints_of_191` show that no 192-edge snake has the same two endpoints as a 191-edge snake, so internal rewiring alone can never reach 192.
- **`DfsCertificate.lean`: a verified exhaustive search.** The module covers the following.
  - `search` is a kernel-evaluable version of the regrowth DFS on 512-bit bitsets. Its pruning bound is the size of a closed reachable region. The region is computed by unverified iteration, and only its closure and start conditions are checked.
  - `search_sound` proves that a `false` result excludes every induced extension of the required length.
  - `no192_from_prefix` turns that into: no `Snake 192` begins with the given prefix.
  - `search_of_children` splits large checks into smaller ones.
  - Kernel memory was the main obstacle. The fixes were bit counting by `R &&& (R - 1)` (proved by `length_le_kcount`) and splitting large trees into child theorems.
- **`DfsBankCert160.lean` (generated by `work/build_lean_certificates.py`).** All 262 oriented bank prefixes with KEEP=160 are kernel-checked: 766 theorems in 40 modules, with large search trees split via `search_of_children` so each check stays under about 2 GB. The aggregate theorem `bank_no192_keep160` says that no `Snake 192` begins with the first 160 vertices of any oriented bank snake (by reversal, none ends with them either). Its axiom audit lists `propext`, `Classical.choice` and `Quot.sound`. Build it with `python3 work/build_lean_certificates.py --keep 160 --shards 40`, then `sh work/run_lean_certificates.sh 160 3`, which builds three shards at a time to bound memory.

- **`DfsDecide.lean` (version 2): an optimized kernel-friendly decision procedure.** It has three parts:
  - `bound2` is the minimum of two verified bounds. The parity bound comes from `ValidExt.parity_counts`. The leaf-peeling bound `peelB` repeatedly removes all vertices with at most one neighbour in the current set, and `peel_sound` proves that a walk entering such a vertex must stop there.
  - Search states are literal numerals produced by the generator (`--v2`), so each instance's ban mask is evaluated by the kernel only once.
  - Large trees are split with `search2_of_children`.

  The compiled search matches the C tool node for node. All 262 KEEP=160 prefixes kernel-check in 3.8 minutes on 3 cores (10.5 CPU-minutes), against roughly 60 CPU-minutes for version 1, and the aggregate `bank_no192_keep160v2` has the same axiom audit. With version 2, `bank_no192_keep152v2` extends this to 152-vertex end segments: 2616 kernel-checked theorems in 60 modules covering about 2.2e5 search nodes, in 40 minutes on three cores, with the same axiom audit.

The C tool's FIFO-label form of leaf peeling is not formalized; the Lean version uses the equivalent simultaneous-round form. Every DFS result above that is not listed in this section remains an uncertified computation.

## Recommended next steps

1. **Classify long Q8 snakes, then settle the single-crossing case exactly.** The rigidity result suggests that 98- and 97-edge Q8 snakes fall into few symmetry classes. Östergård-Pettersson-style orderly generation with canonical augmentation, or a request to those authors for their data, would give the full list. The (98,97) and (98,98) questions then reduce to finitely many partner checks, one per class pair and placement, and could be settled outright.
2. **Push regrowth to KEEP 96-88.** That needs symmetry or memoization, such as caching (head, free-region) states, or a stronger bound based on subcube packing.
3. **Generate new 191-edge snakes from scratch rather than from the bank.** Internal rigidity means the bank is a set of isolated points. Beam search or nested Monte Carlo with the bitset kernel, seeded from different Q8 halves, is the realistic way to reach new basins.
4. **Do not spend more time on internal-window swaps** of bank snakes; sections 2 and 3 show they are almost frozen.

## Reproduce

```sh
cc -O3 -march=native -o work/snake_dfs work/snake_dfs.c
python work/dfs_controls.py
python work/dfs_driver.py regrow --keep 112 --workers 12
python work/dfs_driver.py combo --seconds 1500 --workers 12 --seed 1
python work/dfs_driver.py partner --target 97 --min 85 --nodes 3000000000
```

Window rigidity, from the repository root (prints one line per window):

```sh
python -c "import json;[print(len(e['vertex_sequence']),*e['vertex_sequence']) for e in json.load(open('work/bank9.json'))[:6]]" | ./work/snake_dfs window 9 60 6 1000 200000000 3
```

Q8 seed enumeration (`SNAKE_ENUM` prints every completion up to the cap):

```sh
python -c "import json;v=json.load(open('outputs/snake8_witness.json'))['vertex_sequence'];print(len(v),*v)" | SNAKE_ENUM=100000 ./work/snake_dfs regrow 8 40 99 20000000000
```
