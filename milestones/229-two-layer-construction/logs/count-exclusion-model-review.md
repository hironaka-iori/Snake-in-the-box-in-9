# Round 229 crossing-count exclusion review

No blocking defect was found for the pinned width-46 input and saved native premises. The new constraints preserve every actual candidate that remains possible under those premises. They introduce neither a total crossing cap nor a boundary-omission condition. No worker, solver, compiler or software test was run, and the live unrestricted-crossing outcomes were not inspected.

Read all of `prepare_count_exclusions.py` (30 lines), `joint_count_exclusions.py` (92) and `run_count_exclusions.py` (58), and the complete diffs against the reviewed unrestricted worker and runner. Inspected the completed four-crossing cover, its pinned baseline and reduction inputs, and the terminal six-crossing result and execution receipt. This review concerns the additional inference and input identity; it does not replay the prior solver contradictions or rebuild the complete four-crossing reduction.

## Same-context premises

The four-crossing premise is `coverage46.json`, with status COMPLETE_NATIVE_EXCLUSION, width 46 and 315 contexts. Its table contains every ID 0 through 314 once, with no unresolved status. It comprises 106 static, 96 reduced-pair, 24 direct-pair and 89 boundary-template exclusions. Its explicit scope is the fixed normalized bank-123 seed, appended endpoint 24, two length-preserving replacements, retained anchors and outside positions, and exactly four coordinate-8 crossings. Its proof dependencies include the earlier native width-45 closure; they do not include this strengthening or the unrestricted search.

Every top-level cover pin matches. The pinned baseline directly identifies the current `regions46.json` hash, and all of its context intervals agree with that file. The boundary-reduction pins also match, and the direct four-crossing results identify the same source hash. Thus the four-crossing premise addresses precisely the same geometric contexts as the new worker.

The six-crossing receipt is ACCEPTED_NATIVE_RESULT with exit code zero and no external stop. Its result hash, all execution pins, worker hash and source hash match. The result has 209 distinct rows, exactly the source's PENDING IDs, with 200 INFEASIBLE and nine UNKNOWN. Every saved interval agrees with its source row. There is no witness and there are no cycle cuts.

The nine unknown IDs are `13, 14, 15, 18, 42, 58, 59, 60, 87`. The new worker selects the six-crossing exclusion set strictly from rows whose status is INFEASIBLE, so none of these nine receives that exclusion. The result's COMPLETE_COVERAGE label is not used to turn unknown outcomes into infeasibility.

## Validity of the two added inequalities

For a context, let \(f\) be its unchanged coordinate-8 crossing count and \(c\) the selected crossing count inside the two replacements. The final crossing count of an actual candidate is \(f+c\); the appended edge from 88 to 24 is not a coordinate-8 edge. The saved source field is \(4-f\), as independently reconstructed in the six-crossing review on the same immutable input.

The unconditional new constraint within every queried context is

\[
c\ne4-f.
\]

An actual candidate violating it would have exactly four total crossings, contradicting the complete same-context four-crossing premise. In each of the 200 six-crossing-infeasible contexts the additional constraint is

\[
c\ne(4-f)+2=6-f.
\]

An actual candidate violating that constraint would have exactly six total crossings, contradicting that context's completed six-crossing result. These are the only added model inequalities. The source field is used solely to identify forbidden values; it is not an upper bound.

These inferences need hold only for actual induced replacement paths. They can remove disconnected-cycle selections that satisfy the broader degree relaxation without corresponding to any candidate. Removing such selections is consistent with the intended necessity claim. The resulting model's justification explicitly includes the native four-crossing cover and the applicable six-crossing rows.

## Preserved search and witness conditions

The per-part parity variable retains the bound based on the actual number of available vertical edges, `len(edges)//2`. There is no prescribed total, count cap, boundary selector, mutual-contact condition or short-move closure requirement. Other crossing counts remain permitted subject to the unchanged necessary geometry, parity and face-capacity constraints.

Selected size, colour counts, induced degrees, cross-block disjointness/nonadjacency, cycle cuts and full witness reconstruction are unchanged from `joint_free.py`. The complete witness audit still checks 193 distinct vertices and every pair for exactly consecutive adjacency, then records the actual coordinate-8 crossing count. The 106 initial static exclusions remain crossing-independent. The retained inherited-exclusion branch is unreachable because the current source has no such rows.

The new runner changes the worker filename and adds the four-crossing cover, six-crossing results and their execution receipt to its pins. The worker verifies the cover's status and width, its dependency hashes, and the six-crossing receipt and result links before building models. This checks the current immutable evidence identity; it is not a generic proof that arbitrary future replacement files describe equivalent contexts.

A future infeasible strengthened row establishes a conditional native exclusion using these prior premises. Unknown, timed-out or interrupted strengthened rows still establish no exclusion. Even a complete result remains restricted to this fixed seed, endpoint 24, retained indices and anchors, and two width-46 length-preserving replacements. This review supplies no new witness, unrestricted search outcome, Lean contradiction certificate or global bound.

## Evidence hashes

| File | SHA256 |
|---|---|
| `scripts/prepare_count_exclusions.py` | `54340e8f2d573cb4455cf37fc486958a911b8d647817aada2ba4e93359a26bc3` |
| `scripts/joint_count_exclusions.py` | `9417dc0a324a80f7449f2342323eaf005d5738154768fa859ece334d791ccbb2` |
| `scripts/run_count_exclusions.py` | `605a91f06ed8a86181ad0cd0f4a9ba9e399abd390d1546101399adc76522281d` |
| `data/coverage46.json` | `ee942f3ecc3bd7b1fbf665f5d345db10d0ef8153c62ea9c87dfff8189347d6a2` |
| `data/six46.json` | `264151fb16f02911a84eaedd98d86603c794536a94a0748136068c2600293256` |
| `data/six46-execution.json` | `8ade1250c827e8cddf089a7d05d8e3eb900077c07fbf0c5643bba2022442aadd` |
| `data/regions46.json` | `94ea1833e98f07b3f4327b2f06056847474c75dbcda1f30cb2abe7bb4bd9cca6` |
