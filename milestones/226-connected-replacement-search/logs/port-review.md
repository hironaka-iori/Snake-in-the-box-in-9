# Round 226 upper-suffix and port review

Conclusion: the two suffixes exhaust the actual first replacements for the specified 11 contexts. The port models correctly fix their upper selections while retaining the reviewed boundary constraints. All four requested native batches are now terminal. Their combined cover excludes contexts 191, 200, 202 and 203, leaving 42 of the 301 width-44 contexts unresolved at this review snapshot.

## Read scope

Read all 29 lines of `scripts/upper_suffixes.py`, every record of `data/upper-suffixes.json`, all 97 lines of `scripts/joint_port.py`, its complete diff from `joint_boundary.py`, and the complete wrapper diff from `run_boundary.py` to `run_port.py`. Independently checked the literal domain geometry and the terminal result associations. No enumerator, solver, compiler or software test was run; the computations here were read-only data comparisons, cube-adjacency arithmetic and hashing.

## Why the first crossing count is exactly one

The 11 selected contexts are exactly the boundary search's still-unknown contexts with opposite-face first anchors: 191, 194–203. Every first anchor pair is (18,480), so its crossing count is positive and odd.

Contexts 191 and 203 have total replacement crossing budget two and opposite-face second anchors. Each second path needs at least one crossing, leaving exactly one for the first; their allocation is (1,1).

Contexts 194–202 have total budget three and same-face second anchors. The second anchor face has only 13 domain vertices in contexts 194–199 and 14 in contexts 200–202, below the required 45. The second path therefore needs at least two crossings, leaving exactly one for the first; their allocation is (1,2). The face-shortage argument is needed for these nine cases. In the two opposite-face cases, endpoint parity already supplies the second-path minimum.

These conclusions are conditional on the separately audited prepared domains and fixed seed/endpoint/crossing family. They do not restrict arbitrary paths elsewhere in the cube.

## Complete suffix geometry

For each of the 11 literal first domains, independently recomputed the upper-face component containing terminal anchor 480. It is exactly {480,488}; all saved upper-domain lists match the input, including the additional upper vertices in other components. The edge 480–488 exists because their xor is eight.

After its unique lower-to-upper crossing, an actual first path stays in the upper face until 480. Its upper suffix is therefore a simple path ending at 480 in this two-vertex component. The only possibilities are [480] and [488,480]. The associated lower crossing vertices are 480 xor 256 = 224 and 488 xor 256 = 232; both are present in every first lower domain.

The source's backward search begins at 480, extends by every unused adjacent upper vertex, and excludes adjacency to any earlier nonconsecutive vertex. It records a reversed suffix exactly when the vertical lower port is available. On these domains it visits the two prefixes [480] and [480,488], giving the two saved suffixes. A possible suffix is a necessary decomposition; the enumeration does not claim that a compatible lower path exists.

A 44-edge replacement has 45 vertices. With one upper vertex it has 44 lower vertices and 43 lower edges; with two upper vertices it has 43 lower vertices and 42 lower edges. Thus the saved lower-path lengths 43 and 42 are correct. The lower path always starts at 18, while its endpoint is respectively 224 or 232.

## Port and boundary encoding

The new model accepts only ports 224 and 232 and checks the first anchors (18,480). It fixes every first-domain upper vertex to the indicator of [480] or [488,480], then selects the corresponding lower port. Fixing all other upper components to zero is valid because an actual one-crossing path cannot visit them before ending at 480.

For the singleton suffix, the selected terminal anchor 480 has only the intended vertical neighbour 224 among the chosen suffix/port vertices. For the two-vertex suffix, anchor degree one forces 480's neighbour to be 488; selected vertex 488 has its other path neighbour at lower port 232. Selecting 224 as well would give anchor 480 an extra selected neighbour and is excluded by the existing degree row. Thus the set constraints have the stated suffix interpretation for actual induced paths.

Inspected the saved case-202 model rows: all 13 first upper-domain variables have the expected unconditional zero/one equalities, and each selected lower port has an unconditional equality to one. No expected suffix row is missing. The ordinary degree, cardinality, cube-parity, crossing-budget and cross-path constraints remain unchanged.

The two boundary selectors are unchanged: a true selector implies omission of both original boundary-adjacent vertices in its own block, and their Boolean OR requires at least one qualifying block. Absent-domain boundary vertices are already omitted. The previously reviewed width-43 dependency therefore remains explicit. The wrapper additionally pins `upper-suffixes.json`; all saved enumeration pins and current execution pins match. The geometric completeness argument applies to these enumerated contexts; the port worker is not a universal two-branch reduction for arbitrary inputs merely sharing an anchor value.

## Terminal native outcomes

Outcome inspection was limited to terminal receipts. Both single-context case-202 queries have accepted exit zero and one `INFEASIBLE` result, one for each port. This closes context 202 within the restricted family.

The two ten-context batches also became terminal during review. Each has accepted exit zero, complete coverage of exactly 191, 194–201 and 203, no witness and no added cycle cuts:

| Port | Infeasible IDs | Unknown IDs |
|---|---|---|
| 224 | 191, 200, 203 | 194–199, 201 |
| 232 | 191, 194–201, 203 | none |

Only contexts excluded in both branches are closed. Including the separate case-202 cover, the four new exclusions are 191, 200, 202 and 203. The other seven enumerated contexts retain the unresolved port-224 branch. The prior 46 open width-44 contexts therefore reduce to 42. No unknown branch is counted as infeasible.

Recomputed hashes match every terminal worker/input/coverage/enumeration pin, all exported model hashes, result hashes and stdout/stderr hashes. This verifies saved associations and source scope; it is not an independent solver contradiction replay.

## FaceCounts226 status

Read the complete source of `FaceCounts226.lean` and its accepted receipt and compiler reports. The 24 embedded literal second-domain lists exactly match the corresponding prepared width-43 input lists. Its two theorems calculate the upper-face counts and show each is below 44. The receipt reports `PASS`, exit zero, and both declarations use only `propext`; source, log, object and dependency hashes match.

This is checked arithmetic on the 24 literal width-43 lists. It does not certify the width-44 upper-suffix enumeration, the port solver contradictions, or derivation of the prepared domains from all actual candidates. Those scopes remain separate.

## Frozen hashes

| Artifact | SHA256 |
|---|---|
| `scripts/upper_suffixes.py` | `59cdfe0fad728fa9b9d483411c8df780794c2f7f45173adb2f51a2fd289f4d30` |
| `data/upper-suffixes.json` | `c3e709d44876c6554517c7f761431c730e7804f2b92834a17cb500535f98d060` |
| `scripts/joint_port.py` | `a1a577b5d1103f898e6686ccd04c5b30e57cbb0c38a9bd46feed89a149d853f6` |
| `scripts/run_port.py` | `2113a4f587ab86f3a9f0c2acc2447808181d6e82454b964b108b15081aef3910` |
| `data/port202-224.json` | `bdf43e268af5746c4554f9a34b686e599cb3dcc6a0da69465880379a5404d5f7` |
| `data/port202-224-execution.json` | `bb907e38523f952adbce650a1ec2e4e730ce6eb9ef000da063320ebf4d1374a7` |
| `data/port202-224-202.pbtxt` | `926a16219953f2645703329bbc5175832515beb904407b5188a321a07d8ec575` |
| `data/port202-232.json` | `cf37228a217d1bc0d6310011c1d5e8f7df01dbe8d93df1e959057fd0826726a4` |
| `data/port202-232-execution.json` | `3799bb914ff4aa7b94e59828115c0dc58021867542723335eb30af9f0df9079d` |
| `data/port202-232-202.pbtxt` | `ff7f4176d6450c905c44978f1570d56224a4db1408e68332ae69b64009eafd06` |
| `data/ports44-224.json` | `8819777da6d712772aa20ee99953a6f774bb582c1aeabfb68ccbc45d4c7df058` |
| `data/ports44-224-execution.json` | `db28d53d48463f2f68b7e3026faa193a840ffe92117b0151ffb1170c6ec18bc2` |
| `data/ports44-232.json` | `4e854615c0e14dd818be81e97fbef8b2c733a443c32b343e0baba08481600073` |
| `data/ports44-232-execution.json` | `2030f147216be2593b319d6740391a343e54b9626858e64c4e78a6369d3f311b` |
| `lean/FaceCounts226.lean` | `fd93ada86ff98f6600e7ad38722721654eb4542e9f45b6050d9ef634861c4b2b` |
| `data/FaceCounts226-audit.json` | `4852fe593f06130516d0cac982853c5d73715403447910b9b2425f17b98a4918` |

Only this review log was written. Prior sources, checkpoints, evidence and reviews were preserved. No new snake or global bound is claimed.
