# Fixed-majority-colour contraction audit

**Result: no blocking defect found in the specified finite reduction or saved model coverage.** Independently reconstructed the 131 input snakes, all 145 distinct parity classes, all 23,200 enlargements including duplicates, every contraction graph and static exclusion, and all 49 exported circuit models. All 49 saved query results are `INFEASIBLE`, with accepted execution receipts and matching hashes.

The resulting exclusion is restricted to a candidate 192-edge snake whose **97-vertex majority colour class contains one entire 96-vertex parity class of a saved seed**. It does not exclude keeping a saved 96-vertex class as the candidate's minority class. There is no global Q9 upper-bound consequence.

## Mathematical reduction

A 192-edge path has 193 distinct vertices. Because cube adjacency changes parity, its endpoints have the same parity, its majority class has 97 vertices, and its opposite class has 96. If the majority class contains a fixed saved 96-set, it is that set plus exactly one of the other 160 vertices of the same parity.

Fix such a majority set U. Every opposite-colour vertex used by an induced candidate is internal and has exactly two neighbours in U: its two path neighbours. Any further neighbour in U would be a chord. The contraction graph therefore has vertex set U and, for each opposite-colour z with exactly two neighbours v,w in U, an edge v--w labelled z. Contracting the candidate's opposite-colour vertices gives a Hamiltonian path through all 97 vertices of U.

Conversely, a Hamiltonian path in the simple contraction graph lifts to an induced 193-vertex Q9 path by choosing any available label on each successive pair. A label belongs to exactly one unordered neighbour pair in U, and distinct edges of a simple Hamiltonian path cannot repeat that pair, so the chosen opposite-colour vertices are distinct. Same-colour vertices cannot be cube-adjacent. Each chosen label has exactly its two prescribed neighbours in U, so no cross-colour chord occurs. This proves that parallel labels are interchangeable for this existence question; retaining one simple edge per pair loses no candidate.

An isolated vertex, more than two vertices of simple degree one, or disconnectedness prevents a Hamiltonian path. Parallel-edge multiplicity does not invalidate these conditions. The implementation uses simple degrees for these exclusions and retains all labels for reconstruction.

## Independent finite reconstruction

The audit read the saved bank and recomputed every pairwise adjacency condition on each input path: 192 distinct vertices in Q9, with adjacency exactly between consecutive positions. Both parity classes have size 96. Exact set equality, preserving recorded origins, gives the saved 145 bases from 262 seed/parity occurrences.

For every base the audit enumerated all 160 permissible additions and reconstructed neighbour intersections using explicit nine-neighbour sets, independently of the producer's bit-mask calculation. Every case ID, base, added vertex, labelled/simple edge count, static certificate, surviving graph, and duplicate target matched the saved data.

| Item | Independently verified count |
|---|---:|
| Saved seed paths | 131 |
| Distinct 96-vertex parity sets | 145 |
| Base/addition pairs | 23,200 |
| Distinct enlarged 97-sets | 23,127 |
| Duplicate enlargements | 73 |
| Isolated-vertex exclusions | 17,271 |
| More-than-two-leaves exclusions | 5,807 |
| Disconnected exclusions after those conditions | 0 |
| Surviving graphs | 49 |

The 73 duplicate records identify literally equal sorted 97-sets. The producer's key stores the high and low bytes of all 97 sorted vertex values, which is injective on this fixed-length representation. No coordinate permutation, translation, or broader symmetry identification is claimed or needed.

Across the surviving graphs there are 109–126 labelled edges and 109–123 simple edges. All reconstructed survivor lists, including labels and leaves, agree exactly with `colour-survey.json`.

## Circuit encoding and complete saved-query coverage

For each simple graph, `hamilton.py` introduces both directed orientations of every simple edge and both orientations between every original vertex and a new dummy vertex. Its one `AddCircuit` constraint has no self-loops. Every index 0 through 97 occurs, so the documented circuit semantics require all 98 vertices to be on the single selected circuit. Removing the dummy gives a Hamiltonian path with unrestricted endpoints. Any Hamiltonian path can be extended through the dummy, proving the reverse implication.

The installed `ortools/sat/python/cp_model.py`, lines 578–602, explicitly states that an omitted circuit vertex requires a true self-loop. Thus the no-self-loop encoding does not permit omitted original vertices or a collection of disconnected cycles.

The audit parsed each of the 49 saved `.pbtxt` files without importing or invoking the solver. For every model it verified the complete Boolean-variable list, exactly one circuit constraint, all directed arc endpoints, consecutive positive literal indices, and absence of additional fields/constraints or self-loops. The expected arc sets were reconstructed from the independently verified graphs. There are 20,998 Boolean variables across all models, ranging from 412 to 440 per model. Every model hash matches its saved result row.

The ordered result IDs exactly equal the 49 survivor IDs, with no omitted, duplicated, or extra query. Every result is `INFEASIBLE`; there are no `UNKNOWN`, resource-stopped, or witness rows. `COMPLETE_QUERY_BATCH` by itself only records that all queries ran, so the separate check of all 49 statuses is essential and was performed.

The lift's full pairwise validation is present in the successful-solution branch, but that branch was not exercised because no witness was returned. The written equivalence above supplies the model justification independently of that branch.

## Execution and integrity evidence

Both wrappers preserve source/input hashes, result hashes, and stdout/stderr hashes. The audit recomputed every listed pin and both result/log hashes; stderr is empty and stdout summaries agree with the saved JSON. Both execution records have exit code zero, no stop reason, and status `ACCEPTED_NATIVE_RESULT`.

| Run | Wrapper seconds | Sample count | Maximum sampled private bytes | Minimum sampled free bytes |
|---|---:|---:|---:|---:|
| Colour survey | 3.313 | 15 | 44,937,216 | 1,009,573,888 |
| Hamiltonian batch | 8.484 | 39 | 70,348,800 | 956,747,776 |

All resource samples have empty error and Lean-process lists. The maxima are sampled observations, not continuous peak-memory guarantees. The producer's own reported calculation times are approximately 2.062 and 2.078 seconds; these differ from wrapper duration and are not comparative performance claims.

The wrappers' pins do not constitute a complete solver-binary/environment manifest. No independent solver rerun, contradiction-certificate replay, Lean proof of the finite exclusions, or end-to-end checked model extraction was performed. The 49 exclusions remain accepted native solver results. This audit independently verifies their mathematical model, exhaustive finite coverage, saved bytes, and reported execution status.

## SHA-256 pins

| File | SHA-256 |
|---|---|
| `milestones/203-block-symmetry/data/bank9-input.json` | `0b973ddcd371680ad4efe07c01008c29437280514926daf1a67d99b6ba510edb` |
| `scripts/survey.py` | `924cea3a22243188b1923da41c2e78cbcfa5a188fb3cf82c1b8513cc8cc019cd` |
| `scripts/run_survey.py` | `c00d49afde62f4e64aa2c8b48b1f881ca2eb890f0618026dfac78645497ab52a` |
| `scripts/hamilton.py` | `70d4e68283a6c646ff064c7789fca9950e77892b04d1d7031d4a471fb07da4c4` |
| `scripts/run_hamilton.py` | `99fa4b75ba4f17f87319752cb0f199ab3ab5769f89c1eccc789c1cac20b51b66` |
| `scripts/native_resources.py` | `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413` |
| `data/colour-survey.json` | `5e7ee3e1e685f4715538d155f9d095e303c75f5de48270faead094bd2f569d9d` |
| `data/colour-survey-execution.json` | `064095bf04e21c68f03aaa20795a3e240f9ef3a44e1617ee39ab6b9123c4fe14` |
| `data/hamilton.json` | `331b86545bf4a1c08dbe16e25b846544971969c5ec71092f5b3e259949b2a3f8` |
| `data/hamilton-execution.json` | `58ca2c0867adb3e18d43bc82e2cabfc679fe9aadc86bed0f73f89a3a94d20d72` |

Unprefixed paths in this table are relative to `milestones/231-endpoint-exchanges`. Each of the 49 model hashes is preserved in the pinned `hamilton.json` and was individually checked.

Only this review file was written. No solver, compiler, software test, manuscript edit, or modification of existing research evidence was performed.
