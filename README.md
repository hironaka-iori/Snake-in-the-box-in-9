# Snake-in-the-box in dimension nine

Authors of the manuscript: **Iori Hironaka, Tommy Ma, and Steven Zhan**.

This repository is an ongoing investigation of the longest induced path in the nine-dimensional binary hypercube. Length means the number of **edges**. The exact optimum has not been established by this project.

Research checkpoint: 18 October 2026.

| Claim | Current evidence |
|---|---|
| A 191-edge snake exists | Explicit witness checked in Lean |
| Every snake has at most 255 edges | Lean proof using Huang's degree theorem through pinned mathlib |
| Every selected vertex has at least one singleton coordinate square | Lean-checked for every path length and vertex |
| Every snake has at most 254 edges | Lean-checked end to end by four-corner incidence counting |
| Adjacent internal vertices cannot both have singleton-square count one | Lean-checked geometric exclusion |
| Every snake has at most 251 edges | Lean-checked aggregate consequence of that exclusion |
| Adjacent internal singleton-square counts cannot be 1 and 2 | Lean-checked finite geometric case analysis |
| Every snake has at most 248 edges | Lean-checked end to end, including endpoint corrections |
| Every endpoint has at least four singleton squares | Lean-checked; a checked example attains four |
| Every snake has at most 247 edges | Lean-checked using the stronger endpoint estimate |
| Adjacent internal singleton-square counts cannot be 1 and 3 | Lean-checked symbolic finite-set and endpoint argument |
| Three consecutive internal vertices cannot all have singleton-square count 2 | Lean-checked exhaustive local classification and geometric exclusions |
| Every snake has at most 245 edges | Lean-checked aggregate consequence, with every local premise discharged |
| Every snake has at most 242 edges, and at most 241 edges | Lean-checked end to end: the 22 local count-window exclusions are Lean theorems (geometric bridge, clause soundness, kernel replay of the LRAT refutations by a verified checker); axiom audits on macOS and, from a fresh environment, on Linux |
| At most 239 edges if 145 direction-aware count-window patterns are excluded | Lean-checked conditional theorem (kernel-checked 2592-state potential); the bridge and clause soundness for all 145 patterns are proved in Lean, the kernel replay of their refutations is not yet complete |
| At most 238 edges if 325 five-center window patterns are excluded | Lean-checked conditional theorem (44,064-state potential, kernel-checked in 34 shards); every pattern DRAT-certified |
| The optimum is 196 | Low-confidence independent conjecture; no construction or optimality proof |
| Every internal vertex has at least two singleton squares | False: a Lean-checked 137-edge counterexample |

Start with the [collaborator handoff](COLLABORATION.md) for priorities, exact proof gaps, and search limitations. The [paper](paper/snake9_research.tex) contains mathematical exposition, proofs, explicit transition sequences, and references. It deliberately keeps implementation identifiers outside the paper.

## Repository structure

- `paper/`: all maintained LaTeX sources, including the main paper and the collaborator's DFS report.
- [milestones/](milestones/README.md): separate folders for each research task, its status, notes, and dedicated new artifacts.
- `work/final_lean/`: shared standard-library Lean project, including the new DFS modules.
- `work/spectral/`: shared mathlib-dependent proofs and reproduction tools.
- `outputs/`: historical machine-readable evidence at stable reproduction paths.
- `othercontributors/`: locally supplied contributions awaiting comparison or integration.

## Files

- `paper/snake9_research.tex`: current manuscript, with authors Iori Hironaka, Tommy Ma, and Steven Zhan.
- `work/final_lean/`: authoritative standard-library proof project, with the maintained core and integrated DFS modules.
- `work/spectral/`: authoritative mathlib-dependent bounds 241, 242, 245, 247, 248, 251, 254, and 255, with reproduction instructions.
- `work/spectral/stronger/`: 150 maintained geometric, classification, and aggregate proof modules.
- `RESEARCH_LEDGER.md`: continuing research status, evidence, and unresolved directions.
- `work/*.py`: independent verification and experimental search programs.
- `work/bank9.json`: 131 nine-dimensional examples extracted from the cited published dataset.
- `outputs/*.json`: witness data and recorded experimental results.
- `outputs/*investigation.md`, `milestones/01-foundations/trend_hypothesis.md`: detailed research notes.
- `outputs/*lean-build.log`: proof-checking evidence from the local research environment.

Old PDF exports, compiled proof caches, large upstream downloads, installed dependencies, and local workspace metadata are excluded. The LaTeX source is the current paper. Older notes can refer to local ZIP snapshots that are not needed to use this repository.

## Reproduce the core proofs

Install the toolchain specified in `work/final_lean/lean-toolchain` (Lean 4.19.0), then:

```sh
cd work/final_lean
lake build
```

This project uses Lean's standard library. Its theorem audits contain only the standard logical foundations, with no proof placeholders, custom optimality axioms, or unchecked native computation. It proves the 191-edge witness, the general singleton-square lemma, several construction and exclusion reductions, and explicit counterexamples. The mathlib-dependent [incidence and spectral project](work/spectral/README.md) proves the upper bounds 245, 247, 248, 251, 254, and 255. The strongest proof combines endpoint singleton counts at least four, count-one neighbors at least four, and exclusion of three consecutive count-two vertices. A finite potential argument gives `3*T >= 7*v+5`; the incidence identity then gives at most 245 edges. The current Lean-checked interval is **191 <= a(9) <= 245**; exact optimality remains unresolved.

With the pinned mathlib checkout prepared as described in `work/spectral/README.md`, reproduce the bound 254 from the repository root:

```sh
python work/spectral/verify_incidence.py --mathlib-dir /path/to/mathlib --fresh-core
```

The optional `--fresh-core` flag rebuilds a source-only copy of all current core modules before checking the incidence theorem.

Reproduce the stronger bound 245 and its transitive axiom audit with:

```sh
python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib \
  --core-targets LocalWindowRefuted LocalWindowBridge Snake9 PathStructure CubeLocal \
                 SquareCounterexample SingletonSquareLemma OptimalityTarget \
  --core-jobs 3 --core-heavy-jobs 2
```

The `--core-targets` above include the 1086-module certificate closure of `LocalWindowRefuted`, which the final audit of 241 and 242 imports; choose `--core-heavy-jobs` as about (RAM in GB - 4) / 5. This always builds a source-only core and all strengthening modules in a new directory. It saves source hashes, compiler output, and axiom audits, and rejects any final theorem using foundations beyond `propext`, `Classical.choice`, and `Quot.sound`. The core prefix theorem verifies that excluding a snake of length L+1 excludes every longer snake.

The fresh source-only reproduction succeeded for all 148 strengthening modules, the core, the incidence theorem, and the final audits (151 steps). Every recorded source hash matches the maintained source. Evidence is saved in `outputs/strengthened-reproduction-manifest.json` and `outputs/strengthened-reproduction.log`, with identical versioned copies under `outputs/strengthened-245-reproduction-*`. An independent final import audit also passed.

## Reproduce the independent checks and searches

Run Python commands from the repository root. Standard-library checks require Python 3.12 or later:

```sh
python work/verify_checkpoint.py
python work/check_snake.py
python work/audit_square_counts.py
```

The first command reads and checks the four supplied witnesses and all 131 bank entries without changing the saved results. The next two regenerate particular witness and square-census outputs. These Python checks supplement the Lean proofs.

Solver experiments require OR-Tools 9.15.6755:

```sh
python -m pip install -r requirements-search.txt
python work/exact_search.py --n 9 --edges 192 --seconds 300
python work/neighborhood_search.py --removed 2 --seconds 10 --count 131
python work/layer_search.py --seconds 60
```

Searches may overwrite their result files. Preserve an existing run before repeating it. `UNKNOWN` is unresolved. A restricted `INFEASIBLE` result covers only the encoded family. No solver impossibility result has been certified in Lean or proved the global optimum.

The source-data extraction program `work/verify_bank.py` additionally needs the upstream `record_snakes.csv.zip` and extracted CSV in `work/`; these large files are excluded. The nine-dimensional subset needed for the supplied experiments is included.

## Sources and attribution

The published 191-edge witness and bank derive from [Orland et al., version 3](https://arxiv.org/html/2607.15270v3) and the [Math-AI-Caltech dataset](https://github.com/Math-AI-Caltech/Snake-in-the-Box). The manuscript distinguishes these published constructions from this project's deductions and experiments. The spectral argument uses [Huang's degree theorem](https://annals.math.princeton.edu/2019/190-3/p06) and its maintained mathlib proof. The first eight exact sequence terms are recorded in [OEIS A099155](https://oeis.org/A099155). Full references appear in the paper.

## Joint construction experiments

A checked decomposition of published bank example 0 supplies compatible Q8 paths of 96 and 94 edges, whose join has 191 edges. The new joint model varies both paths. Its 42 small-cube exhaustive controls and fixed 191-edge benchmark passed. The 196-, 197-, and hinted 192-edge searches each returned UNKNOWN after 120 seconds. See [the joint investigation](milestones/02-layer-constructions/joint_layer_investigation.md) for reproduction and exact scope. The bounds and conjecture are unchanged.

## One-singleton structural restriction

A new checked theorem restricts the two path continuations at a one-singleton configuration under explicit internal-vertex premises: they must use different coordinates of the exceptional pair. A separate Lean-checked example is a 60-vertex forest of 14 paths inside the radius-three ball, with all selected radius-two vertices of degree two and exactly one singleton square at zero. It shows why these local constraints alone cannot prove endpoint proximity. See [the local investigation](milestones/04-singleton-geometry/low_singleton_investigation.md). No numerical bound changed.

## Latest experimental lead

Seven additional ball-model records test the normalized one-singleton configuration at radii four through six. The radius-five forest model is solver-infeasible with at most three interior endpoints and feasible with four. These exclusions are **not Lean-certified**. The [local investigation](milestones/04-singleton-geometry/low_singleton_investigation.md) records the model, all outcomes, reproduction command, and the geometric reduction still required. The verified bounds remain unchanged.

## Exhaustive DFS construction experiments

A standalone C search (`work/snake_dfs.c`, controls in `work/dfs_controls.py`) extends the endpoint regrowth experiments. With the first 112 vertices of either end of every bank snake fixed, no 192-edge extension exists; all 262 runs were exhausted. Internal windows of up to 80 vertices almost always have a unique filling. Because Q9 is bipartite, an internal replacement alone can never yield 192 edges. A random sample of 528 million combined window-and-end moves found nothing longer, and the known 98-edge Q8 snake has no other optimal completion after freeing 59 of its vertices. Except where marked as Lean-checked below, these are uncertified exclusions in restricted families. See [the DFS investigation](milestones/08-exhaustive-search/dfs_investigation.md). No bound changed.

## Kernel-checked search (Lean)

Four new modules in `work/final_lean/` use only the standard library. Their axiom audits list only `propext`, `Classical.choice` and `Quot.sound`, with no `sorry` and no `native_decide`.

- `DfsParity.lean` proves that two snakes with the same endpoints have lengths of equal parity. In particular, no 192-edge snake has the endpoints of a 191-edge snake, so rewiring the interior alone can never reach 192.
- `DfsCertificate.lean` (version 1) and `DfsDecide.lean` (version 2) are kernel-evaluable exhaustive regrowth searches on 512-bit bitsets, with soundness theorems connecting a `false` answer to `Snake9.Snake 192` (`no192_from_prefix`, `no192_from_prefix2`). Version 2 prunes with verified parity and leaf-peeling bounds and checks all 262 bank prefixes with 160 fixed vertices in under 4 minutes on three cores.
- `DfsBankCert160.lean` / `DfsBankCert160v2.lean` (generated) prove `bank_no192_keep160`: no 192-edge snake begins or ends with a 160-vertex end segment of any of the 131 bank snakes. With version 2, `bank_no192_keep152v2` extends this to 152-vertex end segments: 2616 kernel-checked theorems in 60 modules covering about 2.2e5 search nodes, in 40 minutes on three cores, with the same axiom audit.

Regenerate and check, from the repository root:

```sh
python3 work/build_lean_certificates.py --keep 160 --shards 20 --v2
sh work/run_lean_certificates.sh 160v2 3
```

The runner builds three shards at a time, because each kernel check holds its memory until the process exits.


## Window exclusions and the bounds 242 and 241

The current potential argument stops at 245 because count sequences repeating `2,2,3` average 7/3. A radius-three local ball model was surveyed for every count triple with entries 1..6. The survey gives an aggregate ceiling of 14/5 for three-vertex windows. One additional four-vertex exclusion, (2,4,2,3), raises it to 3.

The needed exclusions are (2,2,3), (2,2,4), (2,3,2), (3,2,3), (4,1,4..6), and (2,4,2,3), with reversals and every window shape. Each has a CNF certificate verified by `drat-trim`. `AggregateWindowConditional.lean` proves in Lean that these premises imply at most 242 and 241 edges respectively, and the premises are now Lean theorems: `LocalWindowBridge.lean` moves each snake window to canonical position and proves the abstract axioms of `LocalWindowModel.lean` there; `LocalWindowSat/` proves that every clause of each UNSAT core follows from those axioms; and `LocalWindowUnsat/` replays the drat-trim LRAT refutation of each core, segment by segment with `decide +kernel`, through the checker `LratCheck.lean`, whose soundness is proved in Lean. `UpperBound241.lean` proves `upper_bound_242`, `upper_bound_241` and `verified_interval_191_241`; their axioms are only `propext`, `Classical.choice` and `Quot.sound`. Neither drat-trim nor the CNF generator is trusted any more: the LRAT proof is only data for the checker, and every core clause is derived from the snake axioms. The core closure has 1086 modules, 203 of them kernel checks (2.3 kernel-hours on macOS, 5.7 on four shared cloud cores); it was built and audited on macOS (`outputs/upper-bound-241-audit.log`) and again from scratch on Linux (`outputs/upper-bound-241-audit-linux.log`). Build the certificate modules with `work/guarded_lake_build.py`, not a plain `lake build`: each kernel check needs 2-4.5 GB and `lake` would start one per core. See [the milestone](milestones/10-window-aggregate/README.md).

A direction-aware automaton goes further: states remember the shape of the last six transition directions and the last three counts, and a counterexample-guided refinement loop raises the average to 10/3 with 145 solver-refuted windows (each DRAT-verified). The kernel checks the resulting 2592-state potential in about a minute, and `upper_239_of_direction_windows` gives **239 edges** under that premise. With five-centre windows and seven directions of memory the same loop reaches average 7/2 with 325 certified windows, and `upper_238_of_direction_windows5` gives **238 edges**; its 44,064-state table is kernel-checked in 34 shards.

## Collaboration

Use a separate branch for each proof or experiment. Keep claims labeled as proved, conditional, computationally observed, or conjectured. Include transition sequences for every proposed longer snake and verify all unordered vertex pairs. Record solver parameters, seed, time limit, and termination status. Submit changes through pull requests so collaborators can review the mathematical scope as well as the code.

## Integrated Boolean certificate investigation

The separately developed radius-five experiment now has a Lean-checked contradiction for an explicit core of 567 clauses and 252 Boolean variables, using 398 derived clauses. All 41 recorded cycle cuts and the general degree/endpoint clause rules are also checked. The complete interpretation of the concrete input clauses as geometric conditions on a snake is unfinished. See [the certificate investigation](milestones/06-radius-five/ball_certificate_investigation.md) for the evidence boundary and reproduction instructions.

This work does not improve the unconditional bounds. Its earlier conditional 250 arithmetic is retained as historical motivation, rather than a current strengthening target. The exclusion of the singleton-count pattern (2,2,3), the premise of the conditional bound 244, is now one of the 22 Lean-proved window exclusions behind the unconditional bound 241. The Boolean-certificate method may provide an independent route to local geometric exclusions.
