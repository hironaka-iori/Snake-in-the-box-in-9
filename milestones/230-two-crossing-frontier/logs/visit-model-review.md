# Round 230 face-visit model review

Result: no blocking defect found. The crossing restriction and both face-visit inequalities are necessary for every induced candidate in the eleven selected contexts. The saved native results exclude the remaining candidates in these contexts. Combined with the previously accepted 304 unrestricted exclusions, this supports complete native exclusion of the specified two-block width-46 family. It does not establish a global snake bound or a Lean certificate of the complete search.

## Scope

Read all of `close_two.py`, `joint_visits.py`, `run_visits.py`, `FaceVisits230.lean`, and `face-visits-proof.md`; inspected the relevant previous six-crossing and count-exclusion source. Independently reconstructed the exact-two coverage table, checked 46 embedded source/data pins, and checked all fifteen exact-two model hashes. Independently reconstructed every variable domain and every linear constraint in all eleven saved face-visit models, using a small text reader without importing solver software. No solver, compiler, software tests, or process changes were performed.

The previous 304-context unrestricted closure and four-crossing aggregate remain prior native premises. Their pinned bytes, context correspondence, and relevant dependency sources were checked; their complete native traversals were not repeated.

## Exact-two coverage

`two-pairs/result.json` contains exactly IDs 0–14, each with one `INFEASIBLE` iteration, no cycle cuts, and no witness. Every exported model hash matches its row. The execution receipt is `ACCEPTED_NATIVE_RESULT`, exit code zero, with no resource stop; source/input/result/stdout/stderr hashes match.

`close_two.py` requires all fifteen representatives, all eleven supported contexts, no unsupported contexts, nonempty configuration lists, and the accepted execution receipt. Independently reconstructed all 315 output rows: eleven `EXACT_TWO_NATIVE_EXCLUDED` rows contain precisely their configuration lists; the other 304 remain `PRIOR_UNRESTRICTED_EXCLUDED`. No equivalence-based shortcut is used by this cover, since all fifteen queries actually completed.

## Why the total crossing count is at least eight

The eleven contexts are 34, 38, 39, 40, 79, 83, 84, 124, 126, 128, and 129. Independently counted coordinate-8 edges outside both replacement intervals. The first four retain two crossings and the other seven retain one. These edges remain in every candidate, so a zero-crossing candidate is impossible.

Both full-path endpoints, 0 and 24, lie in the lower face. Every coordinate-8 crossing changes face; consequently the total crossing count is even. Exact two is excluded by the new completed cover. Exact four is excluded by the same-width, same-context prior cover. For each of these eleven IDs, the original `six46.json` has an actual single-iteration `INFEASIBLE` result, no cycle cuts, and a matching model hash. No `UNKNOWN` six-crossing row is used. Therefore every remaining candidate must have at least eight crossings.

The source correctly computes the retained count as `4 - row['replacement_crossings']`. The field retains its original four-crossing convention. The model then imposes the lower bound on the sum of selected crossing edges plus this retained count. The appended edge 88–24 changes coordinate 6 and contributes zero coordinate-8 crossings.

The dependency direction is acyclic. The previous count-strengthened searches excluded only the already completed four- and applicable six-crossing counts. Their source does not depend on the present exact-two cover or face-visit result. The current exact-two cover uses the earlier unrestricted exclusions plus the new lower-path queries. The face-visit model is the last step. No boundary cut is imposed in `joint_visits.py`; the historical boundary argument remains confined to the prior four-crossing premise.

## Necessity of the face inequalities

Consider one actual replacement path. Write \(c\) for its crossings, \(u\) and \(l\) for its selected upper and lower vertices, and \(r\) for its number of upper-face anchors.

An interior visit to a face contains at least three vertices. A one-vertex visit would make the two flanking vertices in the opposite face equal. A two-vertex visit would make those flanking vertices adjacent, producing a chord across three path edges. Endpoint visits need only be nonempty.

For \(c>0\), the two endpoint visits are distinct. If there are \(k\) upper visits, crossing incidence and endpoint incidence give

\[
2k=c+r,\qquad u\ge 3(k-r)+r=3k-2r.
\]

Hence

\[
3c\le2u+r,\qquad 3c\le2l+2-r.
\]

For \(c=0\), both inequalities hold by nonnegativity. The endpoint-visit counting identity is unnecessary in that case and must not be applied to a single visit containing both endpoints. The implementation adds only the inequalities, so it handles zero correctly.

The model uses selected vertex counts, not merely allowed-domain sizes. Each crossing variable is exactly the conjunction of its two selected vertical endpoints. Per-part crossing parity is encoded with a nonnegative integer whose upper bound is half the number of available vertical edges. This does not restrict large crossing counts using the historical four-crossing budget. Same-face capacity minima also remain necessary.

These arguments apply to connected induced-path candidates. The initial degree model may admit disconnected cycles. It is permissible to restrict that relaxation by inequalities valid for every actual candidate, even if some disconnected selections fail them. Thus the face inequalities require no unproved acyclicity assumption about arbitrary feasible selected subgraphs.

## Saved models and terminal records

Independently parsed all eleven immutable text models and compared their complete constraint multisets against the geometry and source specification. All vertex counts, anchor conditions, conditional degrees, parity counts, crossing conjunctions, crossing parity, same-face minima, face inequalities, total-crossing lower bounds, and cross-part separation constraints match. All variable names and domains match as well. There are no additional unaccounted constraints.

| Context | Variables | Linear constraints | Retained crossings |
|---|---:|---:|---:|
| 34 | 250 | 745 | 2 |
| 38 | 262 | 823 | 2 |
| 39 | 263 | 834 | 2 |
| 40 | 262 | 836 | 2 |
| 79 | 256 | 789 | 1 |
| 83 | 268 | 861 | 1 |
| 84 | 269 | 872 | 1 |
| 124 | 255 | 795 | 1 |
| 126 | 260 | 826 | 1 |
| 128 | 264 | 861 | 1 |
| 129 | 265 | 873 | 1 |
| Total | 2,874 | 9,115 | |

Every saved model has one completed `INFEASIBLE` solve, no dynamic cycle cuts, and no witness. All model hashes, result/source hashes, accepted execution pins, and stdout/stderr hashes match. The worker reports approximately 1.484 seconds and the wrapper approximately 6.906 seconds. These are recorded times only; no comparative performance conclusion follows.

`run_visits.py` pins the model source, inputs, prior covers, and generic proof receipt. It marks acceptance only for exit code zero without a resource stop and rechecks its pinned bytes. Acceptance alone would not turn an individual `UNKNOWN` into an exclusion; here each of the eleven individual statuses is `INFEASIBLE`.

## Lean scope

The current `FaceVisits230` receipt is `PASS`. Its source, object, compiler log, and all recorded dependency hashes match. The log contains exactly the three reported theorem statements, each using only `propext` and `Quot.sound`:

- `interior_piece_three_vertices` derives the minimum interior-piece size from the exact compatibility and outer-piece separation premises.
- `run_vertex_budget` proves the list-count inequality from explicit size assumptions.
- `face_crossing_budget` combines that inequality with the explicit incidence and endpoint-count identities.

The whole indexed path has not been converted into the required maximal-run lists in Lean. Establishing that extraction, partition identities, and compatibility from the actual cube path remains a separate bridge. Native model generation and solver contradictions are also outside these three results. The written proof supplies the geometric necessity used in this native investigation.

The initial review found an outdated opening in `face-visits-proof.md` saying the source had not been compiled. Its owner subsequently replaced that opening with the accepted source hash and three axiom reports. The final note now agrees with the matching `PASS` receipt. Its final hash is recorded below; the initially inspected note had hash `dcbc6473100fe5a7ce1cdaf4fe4396cd164bfd2841af28ecc0d5764d9725b727`.

## Pins

| Relative path | SHA-256 |
|---|---|
| `scripts/close_two.py` | `a130c81317fe64622895e31e3a9a419db06f75aed834c6b2302e01bfa5ff6a65` |
| `scripts/joint_visits.py` | `3989f1d5562076325cc3cca7e922991b4cbbe076bee79c9e02c9e0033a5684b3` |
| `scripts/run_visits.py` | `abdd8e836a122372a036075da132a73fb372d11f6642834a89f700cca5ece495` |
| `data/coverage-two46.json` | `dcc4c7e7512e50a9322df7ee22d37aed212ee8d0b5299ffafd7d0cb59971af82` |
| `data/two-pairs/result.json` | `851f293f6f29ad2a6ba63f4382a8e93050fa09cb5f5a9e3059b7f6d6cd6f0f49` |
| `data/two-pairs-execution.json` | `1442a16d986261deb28d130f90c2091e7a4db1aa279734cff0c7ecec76bf6f5a` |
| `data/coverage46.json` | `ee942f3ecc3bd7b1fbf665f5d345db10d0ef8153c62ea9c87dfff8189347d6a2` |
| `data/free-summary.json` | `9b3273c9c0b091d05926effa0165553c7e974f78776fb69b4019de0bca9861bb` |
| `data/visits46.json` | `96ff88a257c490cd9226f4ef0810f711d3180d91f4b926987a475ecab1b55c2f` |
| `data/visits46-execution.json` | `9935df896452aaa3f54a6f2e7c4c4ce6b7e106c5d8ab2d2523b77c0470922056` |
| `lean/FaceVisits230.lean` | `d3a99a456f7015a30feade83d9938e80cefd0c2a26ee57de017452b2e8f493c0` |
| `data/FaceVisits230-audit.json` | `ed72162df5d95876b73e3ec83b1169fce49bc8c478008711b040d497b19595e7` |
| `logs/face-visits-proof.md` | `7cb5855e3462aef8bae21771833a3c91ef62e465ade16b1073ce4440bbd245be` |

Accepted Lean compiler-log SHA-256: `6ec474b8e8c2d6367e43e492439206dd849e7b375168af8dfadfb38d156513e6`.

Accepted Lean object SHA-256: `bdafc1e60646fb48db0c57e4921afb9b1eb6f06f8983544e04f7e61ac8d59efe`.

The supported conclusion is restricted to the fixed normalized seed, endpoint 24, retained outside vertices and anchors, and two length-preserving replacements of at most 46 edges. Wider replacements, different seeds or endpoints, and a global upper bound remain outside this coverage. Any final aggregate document requires its own source/status consistency review.
