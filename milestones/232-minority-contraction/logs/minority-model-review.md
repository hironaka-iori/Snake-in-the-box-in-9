# Fixed-minority-colour construction audit

**No blocking defect found.** Independently reconstructed all 145 minority-class cases, all endpoint and internal labels, every static exclusion, and all 81 exported circuit models. The saved results are exactly two `FEWER_THAN_TWO_PORTS`, 62 `UNSUPPORTED_LEAF`, and 81 native `INFEASIBLE` outcomes. No case is omitted or unresolved in this saved family.

## Exact construction criterion

Fix a 96-vertex set U of one cube parity as the complete minority class of a candidate 192-edge induced path. The candidate must have the form

\[
z_0,u_0,z_1,u_1,\ldots,z_{95},u_{95},z_{96},
\]

where the u-sequence lists U exactly once. Every internal opposite-colour vertex has exactly its predecessor and successor as neighbours in U; the two opposite-colour endpoints each have exactly one neighbour in U. Additional neighbours among U would be chords.

Consequently, opposite-colour vertices having exactly two neighbours in U give labelled edges of a contraction graph. Vertices having exactly one neighbour in U give possible endpoint labels at that neighbour, called ports in the code. The desired candidate exists exactly when the contraction graph has a Hamiltonian path whose two ends are distinct ports.

The reverse implication is valid without additional compatibility conditions between labels. An internal label determines one fixed unordered pair of neighbours, so distinct edges of the simple Hamiltonian path cannot share a physical label. An endpoint label has one neighbour in U and cannot equal any internal label, which has two. The two endpoint labels cannot coincide because their singleton neighbours are the distinct first and last vertices of the Hamiltonian ordering. All labels lie in the opposite parity class and are therefore mutually nonadjacent. Their exact neighbour sets in U give precisely the required consecutive adjacencies. The lift has 96 + 95 + 2 = 193 distinct vertices and is induced.

The distinct-port condition is appropriate here because |U| = 96 > 1. A hypothetical singleton fixed set would require a separately stated endpoint-label condition; it is outside this input and implementation scope.

## Static exclusions and circuit model

Fewer than two ports is impossible because a Hamiltonian path on 96 vertices has distinct ends, both needing endpoint labels. A simple-degree-one contraction vertex must be a Hamiltonian endpoint, so a leaf without a port also excludes a candidate. The implemented isolated-vertex, excess-leaf, and disconnectedness conditions are likewise necessary, although none supplies an additional saved classification in this run.

The circuit model includes both orientations of every simple contraction edge and both orientations from the dummy vertex to each port only. It has no self-loops. All 97 vertex indices occur. Thus `AddCircuit` requires a single circuit through all 96 original vertices and the dummy; deleting the dummy gives a Hamiltonian path with both ends in the port set. Conversely, any such path closes through the dummy. Collapsing parallel internal labels and retaining one Boolean arc for each orientation preserves this existence question.

The successful-solution branch reconstructs the full 193-vertex sequence and performs pairwise inducedness validation. No witness was returned, so that branch was not exercised in this run. The mathematical lift argument above does not depend on executing it.

## Independent saved-data verification

`data/bases.json` agrees exactly, including IDs, vertex lists, and origins, with the 145 bases in the already audited round-231 `colour-survey.json`. Its predecessor pin matches. These are the two parity classes of all 131 saved seeds, deduplicated by literal set equality.

For every base the audit independently enumerated all opposite-colour cube vertices and calculated their Hamming-distance-one neighbours among U. It compared the entire saved port dictionary, every labelled edge, all simple degrees, and the status selected by the necessary-condition sequence. Ordered result IDs are exactly 0 through 144.

| Outcome | Count | Independently checked reason |
|---|---:|---|
| `FEWER_THAN_TWO_PORTS` | 2 | Bases 0 and 8 each have exactly one port. |
| `UNSUPPORTED_LEAF` | 62 | At least one reconstructed simple-degree-one vertex has no singleton endpoint label. |
| `INFEASIBLE` | 81 | All static conditions pass and the saved circuit query reports infeasibility. |

Every one of the 81 `.pbtxt` models was parsed without importing the solver. The complete Boolean-variable list, directed edge/port arcs, consecutive positive literal indices, single circuit constraint, and absence of self-loops or extra constraints match the reconstructed graph. The models have 109–124 simple internal edges and 2–17 ports; each has 236–256 Boolean variables, with 20,058 variables in total. Each exported model hash matches its individual result row.

The result is `COMPLETE_QUERY_BATCH`, with no witness. The audit separately checked every status; completeness of the query count alone would not exclude `UNKNOWN` results. No such result occurs here.

The execution receipt is `ACCEPTED_NATIVE_RESULT`, exit code zero, with no stop reason. All source/input/result/stdout/stderr hashes match, stderr is empty, and stdout agrees with the saved result summary. The native worker records 11.390 seconds and the wrapper 17.359 seconds. Its 80 resource samples have empty error and Lean-process lists; maximum sampled private memory is 65,265,664 bytes and minimum sampled free memory is 1,040,687,104 bytes. These are sampled resource observations, not continuous peak guarantees.

## Combined implication with round 231

The proposed combined conclusion is correct within the saved native-evidence scope. Let a candidate have 192 edges, and suppose it contains an entire saved 96-vertex parity class U. Its class of that parity has either 96 or 97 vertices. In the first case it equals U and is covered by this minority-class exclusion. In the second case it is U plus exactly one same-parity vertex and is covered by the complete round-231 majority-class survey.

Therefore no such candidate can contain any entire saved parity class. Relative to each of the 131 saved seeds, a successful 192-edge candidate must omit at least one seed vertex of each parity. This conclusion imposes no old path order, endpoint, crossing count, or replacement-interval restriction. It is still a restricted statement about the saved seed classes and a 192-edge target; it does not establish a global upper bound or classify all possible seed classes.

## Contributor update

A read-only commit-summary and changed-file inspection of `5309471b..61e6655e` finds one commit, `61e6655e7a8aa16ed6f4f56399c381d753a46f5d`. It changes only `lean435/tools/prod435.py` to distribute production claims among helpers. It adds no final upper-bound theorem, assembly source, or theorem-audit artifact. This bounded update supplies no reason to alter the preceding review's maintained upper bound of 233. No contributor worker state, external artifact store, or compilation was inspected here.

## SHA-256 pins

| File | SHA-256 |
|---|---|
| Round-231 `data/colour-survey.json` | `5e7ee3e1e685f4715538d155f9d095e303c75f5de48270faead094bd2f569d9d` |
| `scripts/minority.py` | `260ae79b41d9a75dcf1bd0d5e5c5f65857444332867c0ef60b63e8691dd742fb` |
| `scripts/run_minority.py` | `e9fff5ba0ad15293f2660aab47164c9c0b8beab3d7777d95661c185ae63632c5` |
| `scripts/native_resources.py` | `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413` |
| `data/bases.json` | `ff2356155763cb4bf8f2d1eff80f893021793deca4c76e9183f990ecb6b3297b` |
| `data/minority.json` | `fd1b70411da2b277171ef84cf8a3169d67c1215290b995a123c2aeb67b2a9e48` |
| `data/minority-execution.json` | `58a812adb977c55701c586512caaa8935f36ff1da5c4f1f6fec9d34eee22b442` |

Unqualified paths are relative to `milestones/232-minority-contraction`. The pinned result file contains the 81 individually verified model hashes.

The 81 infeasibility outcomes remain native solver evidence. No solver-binary audit, solver rerun, contradiction replay, Lean compilation, software test, or end-to-end checked extraction was performed. Only this review file was written; existing evidence and manuscripts were unchanged.
