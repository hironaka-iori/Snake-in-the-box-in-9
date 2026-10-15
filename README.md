# Snake-in-the-box in dimension nine

Author of the manuscript: **Iori Hironaka**.

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
| Every snake has at most 245 edges | Lean-checked aggregate consequence, with every local premise discharged |
| The optimum is 196 | Low-confidence independent conjecture; no construction or optimality proof |
| Every internal vertex has at least two singleton squares | False: a Lean-checked 137-edge counterexample |

Start with the [collaborator handoff](COLLABORATION.md) for priorities, exact proof gaps, and search limitations. The [paper](outputs/snake9_research.tex) contains mathematical exposition, proofs, explicit transition sequences, and references. It deliberately keeps implementation identifiers outside the paper.

## Files

- `outputs/snake9_research.tex`: current manuscript, with author Iori Hironaka.
- `work/final_lean/`: authoritative standard-library proof project, with 15 modules.
- `work/spectral/`: authoritative mathlib-dependent bounds 245, 247, 248, 251, 254, and 255, with reproduction instructions.
- `work/spectral/stronger/`: 148 maintained geometric, classification, and aggregate proof modules.
- `RESEARCH_LEDGER.md`: continuing research status, evidence, and unresolved directions.
- `work/*.py`: independent verification and experimental search programs.
- `work/bank9.json`: 131 nine-dimensional examples extracted from the cited published dataset.
- `outputs/*.json`: witness data and recorded experimental results.
- `outputs/*investigation.md`, `outputs/trend_hypothesis.md`: detailed research notes.
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

A checked decomposition of published bank example 0 supplies compatible Q8 paths of 96 and 94 edges, whose join has 191 edges. The new joint model varies both paths. Its 42 small-cube exhaustive controls and fixed 191-edge benchmark passed. The 196-, 197-, and hinted 192-edge searches each returned UNKNOWN after 120 seconds. See [the joint investigation](outputs/joint_layer_investigation.md) for reproduction and exact scope. The bounds and conjecture are unchanged.

## Collaboration

Use a separate branch for each proof or experiment. Keep claims labelled as proved, conditional, computationally observed, or conjectured. Include transition sequences for every proposed longer snake and verify all unordered vertex pairs. Record solver parameters, seed, time limit, and termination status. Submit changes through pull requests so collaborators can review the mathematical scope as well as the code.
