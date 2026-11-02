# Independent review of D01234A1542 as a graph-strengthening candidate

No blocking error was found in this candidate's source identity, proposed counter relaxation, or graph alignment. One reported accepted-key hit was independently verified directly against the Lean graph literals. This remains a candidate review: no new semantic theorem, contradiction proof, or graph certificate was checked by this reviewer. No compiler, solver, or proof replay was launched, and the complete 2,092-hit enumeration was not rerun.

## Source identity and proposed statement

The saved candidate comes from pin `7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b`, family `direction5`, root `D01234A1542`, representative reference-union index 1006. Its actual Cnf declarations and metadata agree:

```text
directions = [0,1,2,3,4]
window     = [0,1,3,7,15,31]
old bounds = [(1,1),(5,5),(4,4),(2,2)]
new bounds = [(0,1),(0,5),(0,21),(0,2)]
```

The target is `Refuted (winOf [0,1,2,3,4]) [(0,1),(0,5),(0,21),(0,2)]`. It would exclude simultaneous inequalities $a_1\le1$, $a_2\le5$, and $a_4\le2$ for this local window, independently of the third count in its natural range. The original exact-count theorem alone does not establish this stronger statement; a new semantic check is required.

All 441 decoded Lean raw clauses were independently compared with the exact `core_ids` subsequence of the pinned 24,359-clause full CNF. Every clause matched, and the decompressed CNF hash agrees with the metadata. This additionally checks source-to-core identity beyond the screening script's length and metadata comparisons. It does not validate a newly generated contradiction proof.

## Counter and tag audit

The Sat source has nine counters. The only counter indices occurring in any clause tag are 0, 1, 3, and 7; these are also precisely the indices used by register variables that appear in the raw CNF. All four occur in `.over` tags. Independent parsing found 147 primary variables, 20 endpoint variables, and 224 register variables among the raw clauses' variables.

The exact edits are:

| Counter | Kind | Old limit | New limit |
|---:|---|---:|---:|
| 0 | `.ends` | 2 | 2 |
| 1 | `.hi 0` | 1 | 1 |
| 2 | `.lo 0` | 20 | **21** |
| 3 | `.hi 1` | 5 | 5 |
| 4 | `.lo 1` | 16 | **21** |
| 5 | `.hi 2` | 4 | **21** |
| 6 | `.lo 2` | 17 | **21** |
| 7 | `.hi 3` | 2 | 2 |
| 8 | `.lo 3` | 19 | **21** |

Counter positions, literals, kinds, register meanings, tags, and raw clauses must remain unchanged. All five edited counters are unreferenced by this core. An independent reconstruction of `ctrOK` from the actual literal meanings and corner lists accepted all nine original counters, and all nine modified counters under the proposed bounds. Each centre has 21 free pairs, as assumed by the screening arithmetic.

The retained clauses include 185 counter tags for counter 0, 40 for counter 1, 6 for counter 3, and 65 for counter 7. The other tags are 6 window clauses, 95 degree-at-most-two clauses, 8 positive-degree clauses, 29 `lowEnd` clauses, and 7 cycle cuts. Consequently the endpoint limit and the full local-axiom interface must be preserved. This core is not justified solely by the three displayed count inequalities and vertex selection.

The existing soundness mechanism can reuse the unchanged CNF: check all modified metadata and clause tags under the new bounds, apply `Tags.sound`, and compose with the checked contradiction using `Tags.refuted_of_sat`. The original `tau` assignment does not inspect the counter limits; the clause checks inspect unchanged limits at the four referenced counters. Successful evaluation of the modified semantic checker remains the necessary next proof step.

## Screening-script review

`screen_small_cores.py` selects the exact metadata family named by each Cnf source, checks the saved metadata hash and key lists, and infers bounds from `.over` dependencies. For this winner, its parsed counter indices, original bounds, proposed bounds, and five edits all agree with the independent inspection. Its four proposed exact-union consequences are indices 1006, 1010, 1011, and 1014. Each has the same direction word and interval bounds contained in the proposal. No reversed direction matching was used to enlarge that reference-key coverage.

`screen_candidate_graphs.py` uses width 4, count offsets $s=0,1,2$, and five-direction slices `D[s+2:s+7]`. Both orientations are needed even though the canonical reverse of `[0,1,2,3,4]` is the same pattern. The count constraints reverse with the slice:

| Orientation | Required symbol inequalities |
|---|---|
| Forward | $a_s\le1,\ a_{s+1}\le5,\ a_{s+3}\le2$ |
| Reverse | $a_{s+3}\le1,\ a_{s+2}\le5,\ a_s\le2$ |

These match the existing interval-exclusion convention and the six-symbol code at actual centres $r+3$ through $r+8$. Caps 1, 5, and 2 are below the truncation threshold; cap 21 allows symbol 6 and all actual counts represented by it. There is no truncation error in these tests.

The script unions placement masks within each direction and then intersects with accepted codes separately for every `(direction, history)` block. This avoids double-counting multiple hits on one key while preserving distinct histories. Its acceptance reconstruction is checked against the preceding graph-test key hash. The report explicitly labels the results hypothetical and leaves the graph unchanged. I verified the hash links between both screening reports, both screening scripts, and `graph-test.json`, plus the current hashes of the direction, diagram, class-root, and block-assignment Lean sources. I did not independently rerun the full enumeration or revalidate every inherited graph dependency.

## Independent first-hit verification

The first reported key is `(direction, history, code) = (4,0,7373)`, encoded as integer 14,004,173. Its direction word is `[0,1,2,0,3,1,4,0,1]`, and its symbols are `[1,6,5,1,5,6]`.

Directly reading the Lean block and diagram literals gives block 300, class 3, root 669, and the accepted traversal

```text
669 -> 532 -> 531 -> 529 -> 527 -> 24 -> 1
```

At count offset 0, the direction slice is `[2,0,3,1,4]`. Reversing and canonicalizing gives `[0,1,2,3,4]`. The reversed centre symbols are `[1,5,6,1]`, which satisfy all four proposed intervals. This is the only matching forbidden placement for that key; the forward orientation fails because its second count symbol is 6. It is an accepted abstract graph key, not a constructed actual snake.

The saved screen reports 2,092 rejected full keys across 489 contexts, with rejected-key digest `0e37ee150d3cb7d62e17146491aa2461b1e4d83944f25ac242ab6c53a6a15fab`. These totals are parent-generated enumeration results reviewed at the source level, not an independent full recount here. Their mathematical use remains conditional on a checked relaxed exclusion and a proved graph-retention update. No new numerical upper bound follows from this review.

## Input hashes

All values are SHA-256.

| Artifact | Hash |
|---|---|
| Candidate Cnf source | `476612a4450c891137bd713f17a274b7e8723ab815eaddeb7d8905b96020f685` |
| Candidate Sat source | `02046cd200a26980ff5c5270b3ab292109f2f9592231bb79dea4540afaa416f8` |
| `lean_core_direction5/d01234_a1_5_4_2.json` | `6d03bb8a0102c834b23a8472164e161b21a1bace92965f6272c068a993e9bedb` |
| Pinned compressed full CNF | `606910417bdf468233237b3ffe99b9c2aaf05c10851bfe13b8eb620dafffff81` |
| Pinned decompressed full CNF | `35ed6ca71c77b6c081ab10ec7999af7f24daaa8674aa2d8b1fc05f4caadd0812` |
| `data/small-core-screen.json` | `8801400798c1d6dca2437d032aa8af4844f5c4bc9b2dbb9b77731fed34b29bc1` |
| `data/candidate-graph-screen.json` | `a83d142547051b647e34bde1c9b1243d578db81f073224e311cf400addb449fa` |

Only this review report was written. Existing screening reports, candidate sources, and graph data were unchanged.
