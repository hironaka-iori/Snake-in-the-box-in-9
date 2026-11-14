# Capacity implementation source review

Result: no unsound capacity rule, input-format mismatch, or continuation omission was found in the reviewed source. This is a bounded source assessment, conditional on the wrapper's validation succeeding with Python assertions enabled. No search, compiler, software test, or process operation was run.

## Mathematical justification

The wrapper declares 32 distinct clique variables, restricts all their domains to the 32 even six-bit words, and checks that every clique pair forbids equal words in the original binary relation. Thus every satisfying assignment uses each even word exactly once on the clique. A word with no remaining carrier proves that the current domains admit no completion; a word with one carrier forces that carrier to the word. Both new clique operations are valid.

Each covered outside variable also has its domain within the even words. Its assigned word therefore agrees with the value of a clique member. The wrapper checks inequality against every clique member outside its listed partner set. Consequently, the outside variable's value must belong to the union of its partners' domains. Intersecting with that union is valid. The geometric description of the partners is unnecessary for this implication once the binary inequalities have been checked.

For the selected census record, case 23 has 81 variables, base coordinates `[0,5]`, a 32-variable even clique, and nine covered variables: `[2,32,60,64,66,70,72,76,80]`. Each has ten partners. The source validation therefore covers 496 clique pairs and 198 outside/nonpartner pairs, checking the 32 equal-even-word entries in each relation. These are counts of the comparisons prescribed by the source; this review did not execute those comparisons on the model.

## Implementation and format

The complete diff from `history_solver.c` adds only capacity data, the two propagation operations, the appended input parser, and three JSON counters. The original branching, saved-frontier construction, binary propagation, forbidden assignments, and lexicographic pruning remain unchanged.

Every new domain change is a strict reduction, queues incoming binary arcs, and marks the outer propagation pass as changed. Subsequent passes revisit both global rules. Unique-carrier forcing cannot underflow its removal counter because the carrier contains the relevant word. An empty covered domain or absent word carrier returns a contradiction. The masks use 64-bit shifts with values below 64, and the size-64 alphabet retains the original special case avoiding a shift by 64.

The wrapper appends, after the original relations, forbidden assignments, and permutations: the clique size, word mask, number of covered variables; the clique indices; and each outside index, partner count, and partner list. The C reader consumes precisely this order. It validates distinct indices, membership in the clique, domain containment, mask size, and partner counts. It does not independently check the binary inequalities: those checks belong to the wrapper. The additional JSON fields preserve the existing status, solution, and pending-domain layout.

`prepare_capacity_engine.py` expresses the same source changes through bounded replacements. Its generated files were inspected directly and compared with the original files; the generator was not executed during this review.

## Continuation and pins

The unchanged recursive search saves the interrupted current branch and, while unwinding, every unvisited sibling value set. Those sets are disjoint; branches already exhausted are omitted. Each branching step fixes a previously non-singleton variable, so the existing pending-array bound suffices. New propagation only removes values proved impossible under the validated capacity premises and does not change this coverage argument.

On a successful child exit, the wrapper checks returned-domain containment and pairwise disjointness, validates any witness against all original constraints, rechecks source/model pins, and requires the current state to equal its saved pre-run bytes. It writes the receipt before atomically replacing the current state. Failed or forcibly stopped child runs leave the old frontier in place. The wrapper does not independently reconstruct exhaustive coverage from output; that claim still depends on the reviewed C control flow and the inherited model/symmetry assumptions.

The capacity runner pins its own source, the capacity C source and executable, the model and resource helpers, the lower-dimensional source, and the capacity census. Case pins add the copied model, permutations, complete input tail, and capacity declaration. Resume requires exact pin equality. A pre-existing state from the original engine is rejected rather than silently reused. The unchanged preparation copies the historical permutation file and then pins it; this review did not independently reprove the model's symmetry reduction.

At the file inspection in this review, `build/capacity_solver.exe` and `data/case-23` were absent. Accordingly, no compiled-artifact, initialized-tail, run-receipt, or runtime-success claim is made. The recorded source hashes below identify the reviewed implementation only.

## Conditions and limitations

- Python `assert` statements enforce essential capacity premises, pin checks, and transition validation. Running with `-O` or `PYTHONOPTIMIZE` would disable these guards. The source assessment assumes assertions are enabled.
- The inherited lock uses an existence check followed by a write, rather than atomic exclusive creation. The stated single-coordinator assumption is required; simultaneous launch safety is not established. Resource inspection detects Lean workers and available memory, rather than every possible native worker.
- A standalone capacity-engine invocation can supply an invalid clique declaration that passes the C parser. Sound use requires the wrapper's relation checks or equivalent independently established premises.
- No runtime behavior, speed improvement, full-model exhaustion, Lean certificate, or new bound follows from this review. Original model completeness and residual symmetry coverage remain inherited obligations.

## SHA-256 source pins

Paths below are relative to `milestones/209-slice-capacity`.

| File | SHA-256 |
|---|---|
| `scripts/history_solver.c` | `5de5aa76686e3cf804da7d6d9dbb2a4202ac44442c5cc1e11fe9a0054cb5f764` |
| `scripts/capacity_solver.c` | `2a4e12272665b3bcac59a32c64d7167e5e343f1174d0592f5945717e2e0f593e` |
| `scripts/continue_search.py` | `78641f36dddce1299c6e3953ae1caaf682cc374f7888c4c43722e4e1ef1e786d` |
| `scripts/capacity_continue.py` | `6aa8325cb39a963d7e21bc6f1f2e720016fedf312f97af5d0b5e21a44b50e67b` |
| `scripts/history_model.py` | `e96cea7d793be2e77022c784179d29ce82f2f5c4cbb51c1840d6dc90deb9ae41` |
| `scripts/native_resources.py` | `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413` |
| `scripts/prepare_capacity_engine.py` | `305ef9538812beb717541e912b0a53ebff58ac7fbf91151f84a6cfbcd08434da` |
| `scripts/analyze_capacity.py` | `9734002500017a13ea79fcdabac9c40d33a5782962aba4ccacf685d59ae932b5` |
| `data/lower-dimensional-input.json` | `d62c92cc97eae196b21aeefe2111adfb03cc3121b9b62ba7e3e2c6ee6920c20d` |
| `data/square-capacity.json` | `400753eef4c691333e5e03d87239d93fe63ea9f7fc870ac1d742a01afb21bb10` |

The selected historical model is `milestones/207-five-history/data/case-6-ordered-from-0-23/model.json`, with SHA-256 `f016ce4f452b404dd9b539218bddd7ae514e75bff5c901ab15a6a586b9df04d3`. Both the historical summary and the selected capacity record identify this hash.

The adjacent historical `permutations.json` hashes to `7e4e3dde90085bc5365ae29d2af69af62281fe52d69ea73482e4ef257a0abb93`; `milestones/207-five-history/data/six-coordinate-summary.json` hashes to `a8c1435ff5dff39711ab2269b0fd24e1f6e386830dad887a58cbba7cfe41a8be`. These are provenance pins, without an additional symmetry-validation claim.
