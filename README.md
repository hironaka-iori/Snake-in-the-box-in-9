# Snake-in-the-box in dimension nine

Authors of the manuscript: **Iori Hironaka, Tommy Ma, and Steven Zhan**.

This repository is an ongoing investigation of the longest induced path in the nine-dimensional binary hypercube. Length means the number of **edges**. The exact optimum has not been established by this project.

Research checkpoint: 15 October 2026.

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
| **Every snake has at most 241 edges** | Lean-checked, unconditional: all window exclusions behind the former conditional 242 and 241 ((2,2,3), (2,2,4), (2,3,2), (3,2,3), (4,1,4..6), (2,4,2,3), every shape and reversal) are kernel-checked refutations of their local CNFs with a formalized geometric bridge (`UpperBound241.lean`, `verified_interval_191_241`) |
| **Every snake has at most 244 edges** | Lean-checked, unconditional: the (2,2,3) window is excluded by a kernel-checked refutation of its local CNF plus a formalized geometric bridge (`UpperBound244.lean`, `verified_interval_191_244`) |
| Every snake has at most 245 edges | Lean-checked aggregate consequence, with every local premise discharged |
| At most 242, resp. 241, edges if five, resp. six, local count-window patterns are excluded | Lean-checked conditional theorems (fresh 156-step reproduction); each window exclusion has a DRAT-checked certificate for a local CNF, not yet a Lean proof |
| At most 239 edges if 145 direction-aware count-window patterns are excluded | Lean-checked conditional theorem (kernel-checked 2592-state potential); every pattern has a DRAT-checked certificate, not yet a Lean proof |
| At most 238 edges if 325 five-centre window patterns are excluded | Lean-checked conditional theorem (44,064-state potential, kernel-checked in 34 shards); every pattern DRAT-certified |
| At most 235 edges if 2,635 six-centre window patterns are excluded | Lean-checked conditional theorem (264,384-state potential, 34 kernel shards); every pattern DRAT-certified |
| At most 232 edges if 15,959 six-centre window patterns (counts lumped at eight, refuted at radius three or four) are excluded | Lean-checked conditional theorem (1,114,112-state potential at mean 9/2 with start-state accounting, 34 kernel shards); every pattern DRAT-certified |
| At most 233 edges if 8,182 six-centre window patterns (counts lumped at eight) are excluded | Lean-checked conditional theorem (1,114,112-state potential at mean 13/3, 34 kernel shards); every pattern DRAT-certified |
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
- `work/spectral/`: authoritative mathlib-dependent bounds 245, 247, 248, 251, 254, and 255, with reproduction instructions.
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

This project uses Lean's standard library. Its theorem audits contain only the standard logical foundations, with no proof placeholders, custom optimality axioms, or unchecked native computation. It proves the 191-edge witness, the general singleton-square lemma, several construction and exclusion reductions, and explicit counterexamples. The mathlib-dependent [incidence and spectral project](work/spectral/README.md) proves the upper bounds 245, 247, 248, 251, 254, and 255. The strongest proof combines endpoint singleton counts at least four, count-one neighbors at least four, and exclusion of three consecutive count-two vertices. A finite potential argument gives `3*T >= 7*v+5`; the incidence identity then gives at most 245 edges. The current Lean-checked interval is **191 <= a(9) <= 241** (`verified_interval_191_241`, 20 October 2026; reproduction `outputs/strengthened-241-reproduction-manifest.json`, 606 steps); exact optimality remains unresolved. It was reached in two steps, 245 -> 244 -> 241, described next. The step from 245 to 244 discharges the premise of the conditional bound `upper_244_of_no_two_two_three`: no snake has three consecutive internal vertices with local counts 2, 2, 3. A cube automorphism normalises such a window to one of two shapes (`CubePermutation.lean`). The snake's vertex set then satisfies every clause used by the refutation of the corresponding radius-three CNF (`W223G1*.lean`, checked clause by clause by a kernel-decided checker with a soundness proof). Both CNFs are unsatisfiable by kernel-checked unit-propagation proofs (`W223*.lean`, 1,629 and 17,101 steps). Everything audits to `propext`, `Classical.choice`, `Quot.sound` (`outputs/strengthened-244-reproduction-manifest.json`, 353 steps). See `milestones/07-window-223/bridge/README.md`.

With the pinned mathlib checkout prepared as described in `work/spectral/README.md`, reproduce the bound 254 from the repository root:

```sh
python work/spectral/verify_incidence.py --mathlib-dir /path/to/mathlib --fresh-core
```

The optional `--fresh-core` flag rebuilds a source-only copy of all current core modules before checking the incidence theorem.

Reproduce the stronger bound 245 and its transitive axiom audit with:

```sh
python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib
```

This always builds a source-only core and all strengthening modules in a new directory. It saves source hashes, compiler output, and axiom audits, and rejects any final theorem using foundations beyond `propext`, `Classical.choice`, and `Quot.sound`. The core prefix theorem verifies that excluding a snake of length L+1 excludes every longer snake.

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


## Window exclusions and conditional bounds 242 and 241

The current potential argument stops at 245 because count sequences repeating `2,2,3` average 7/3. A radius-three local ball model was surveyed for every count triple with entries 1..6. The survey gives an aggregate ceiling of 14/5 for three-vertex windows. One additional four-vertex exclusion, (2,4,2,3), raises it to 3.

The needed exclusions are (2,2,3), (2,2,4), (2,3,2), (3,2,3), (4,1,4..6), and (2,4,2,3), with reversals and every window shape. Each has a CNF certificate verified by `drat-trim`. `AggregateWindowConditional.lean` proves in Lean that these premises imply at most 242 and 241 edges respectively. The premises themselves are **not** Lean theorems. The geometric bridge and the refutations are now formalized for all of these windows, so 242 and 241 are unconditional (above). See [the milestone](milestones/10-window-aggregate/README.md).

A direction-aware automaton goes further: states remember the shape of the last six transition directions and the last three counts, and a counterexample-guided refinement loop raises the average to 10/3 with 145 solver-refuted windows (each DRAT-verified). The kernel checks the resulting 2592-state potential in about a minute, and `upper_239_of_direction_windows` gives **239 edges** under that premise. With five-centre windows and seven directions of memory the same loop reaches average 7/2 with 325 certified windows, and `upper_238_of_direction_windowsK5R3` gives **238 edges**; its 44,064-state table is kernel-checked in 34 shards. Six-centre windows raise the average to 4 with 2,635 certified windows, and `upper_235_of_direction_windowsK6R3W` gives **235 edges** (its 264,384-state table is kernel-checked with packed 8-bit arithmetic, all 46,656 transitions of a shape pair in one big-integer comparison, in about 100 s for the 34 shards and four minutes for the whole chain; the earlier one-transition-per-step chain `upper_235_of_direction_windowsK6R3` took about thirty-five). Radius four at four centres gives no gain. Lumping the counts at eight instead of six (1,114,112 states) and refining with a compiled Howard solver that breaks up to 200 near-minimal cycles per round raises the average to 13/3 with 8,182 certified windows, and `upper_233_of_direction_windowsK6R3C7W` gives **233 edges**. Deciding windows that are feasible in the radius-three ball again at radius four raises the average to 9/2, and charging the start of the walk its own counts (the potential is bounded by the start state's symbol sum instead of its full range) turns 9/2 into **232 edges**: `upper_232_of_direction_windowsK6R34C7W`, 15,959 certified windows. The proof machinery got faster along the way: the cap-7 data module went from 682 s to about 70-110 s (the two potential layouts are related by six delta swaps proved once in `WindowAutomatonTranspose.lean`, instead of a 32,768-step loop per shape), certification shares cycle cuts between windows of a shape (about 1.8 times the throughput), and the reproduction driver checks independent modules in parallel with a dependency-aware cache.

## Collaboration

Use a separate branch for each proof or experiment. Keep claims labelled as proved, conditional, computationally observed, or conjectured. Include transition sequences for every proposed longer snake and verify all unordered vertex pairs. Record solver parameters, seed, time limit, and termination status. Submit changes through pull requests so collaborators can review the mathematical scope as well as the code.

## Integrated Boolean certificate investigation

The separately developed radius-five experiment now has a Lean-checked contradiction for an explicit core of 567 clauses and 252 Boolean variables, using 398 derived clauses. All 41 recorded cycle cuts and the general degree/endpoint clause rules are also checked. The complete interpretation of the concrete input clauses as geometric conditions on a snake is unfinished. See [the certificate investigation](milestones/06-radius-five/ball_certificate_investigation.md) for the evidence boundary and reproduction instructions.

This section predates the unconditional 244 (above). Its earlier conditional 250 arithmetic is retained as historical motivation, rather than a current strengthening target. That target, exclusion of the singleton-count pattern (2,2,3), has since been reached; it discharges the conditional bound 244. The Boolean-certificate method may provide an independent route to local geometric exclusions.
