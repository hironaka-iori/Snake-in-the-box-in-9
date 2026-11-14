# Spare-capacity support review

Date: 2026-11-14. Result: the proposed deduction and inspected native implementation are sound under the stated model inequalities. The original case-22 binary tables satisfy those inequalities. This report covers mathematics, saved model data and source inspection. No compiler, Lean, solver, search or software test was run. Preparation of the appended native input and any state transfer or later search chain require their own evidence.

## Deduction and essential assumptions

Within one parity alphabet of 32 words, the clique variables must receive pairwise distinct words. The outside variables must also receive pairwise distinct words. Every outside variable conflicts with each clique variable except its listed possible partners. All these variables' domains lie within the same parity alphabet. Possible partners need not actually permit equality for every word; including extra partners only weakens the support deduction.

If the clique has size \(c\), exactly \(32-c\) words remain unused by its assigned values. Distinct outside variables whose values occur nowhere in the clique therefore number at most \(s=32-c\). This is the assigned-word inequality in `Spare211.spare_capacity`; it does not require the clique to use every alphabet word.

For outside variable \(i\), let \(P_i\) be the union of the current domains of its listed partners. If \(D_i\cap P_i=\varnothing\), its assigned value cannot equal any partner's value. The nonpartner inequalities exclude all other clique values. It must therefore use one of the unused words. Each such outside variable consumes a different unused word because outside values are pairwise unequal.

Consequently, more than \(s\) such variables makes a satisfying assignment impossible. If exactly \(s\) are already forced to use unused words, every remaining outside variable must share a clique value. It can share only with a listed partner, so intersecting its domain with \(P_i\) preserves every satisfying assignment. The forced variables themselves must retain their unshared options. If the forced count is smaller than \(s\), this argument permits no support filtering of the remaining variables.

For retained coordinates \([0,6]\), the even family has 30 clique and 9 outside variables, leaving two unused words; the odd family has 26 clique and 13 outside variables, leaving six. These are separate inequalities in separate alphabets. No claim requires every parity word to occur, prescribes a specific partner, or permits unconditional support filtering of every outside variable.

## Independent saved-model inspection

The case-22 model at `milestones/207-five-history/data/case-6-ordered-from-0-22/model.json` has 78 variables, 2,600 binary relations, 120 nogoods, retained coordinates `[0,6]`, and free coordinates `[1,2,3,4,5,7]`. Its exact hash agrees with the round-209 census.

Both families' clique and outside lists contain distinct, disjoint variable indices; their domains lie in the designated 32-word parity alphabets. Partner keys exactly cover the outside list, and every partner list is distinct and contained in its clique. Direct inspection of the original binary tables establishes all required equal-word exclusions:

| Family | Clique pairs | Outside pairs | Outside/nonpartner pairs | Inspected diagonal entries |
|---|---:|---:|---:|---:|
| Even | 435 | 36 | 189 | 21,120 |
| Odd | 325 | 78 | 228 | 20,192 |
| Total | 760 | 114 | 417 | 41,312 |

Every listed pair has an original binary relation, and every corresponding parity-word diagonal entry forbids equality. These are concrete necessary constraints of the saved model. This inspection does not establish the complete geometric interpretation of every model solution or search branch.

## Implementation and source comparison

`spare_solver.c` is derived from round-209 `history_solver.c`. Its exact diff adds only the support-family structure, support propagation, appended-input parser and four output counters. The C `visit` body is exactly unchanged. Binary propagation, lexicographic restrictions, nogoods, branching order, stop handling and pending-domain construction retain their previous source.

The new propagation computes `spare` from the declared word-mask population minus clique size. It builds each outside variable's partner union from current domains and marks it forced precisely when the intersection is empty. It rejects only when the forced count exceeds the spare count. Equality triggers intersections for nonforced outside variables only. Empty domains reject; other removals enqueue binary neighbours and set `altered`, causing another outer propagation iteration.

Within a family, the cached unions and forced flags remain valid during filtering: all partner indices belong to its clique, while only disjoint outside domains are modified. Each later family recomputes its own unions from current domains, as does each new outer iteration. The implementation contains neither the old saturated-clique every-word-used rule nor matching/subset propagation.

The parser accepts one or two families, checks clique size against the word-mask population, checks the mask against the alphabet, and bounds all arrays and variable indices. It enforces distinct clique members, distinct outside members disjoint from the clique, domain containment in the declared word mask, and distinct partner lists contained in the clique. Zero partner counts are permitted and correctly force such a variable unshared. These guards keep the spare count nonnegative and all mask shifts and array accesses within their declared ranges.

The parser does not independently establish pairwise clique inequality, pairwise outside inequality, or the outside/nonpartner inequalities. The prepared input must therefore bind the exact families and masks to the independently inspected original binary tables above. Merely satisfying the parser's structural checks is insufficient.

`spare_continue.py` differs from the frozen round-211 continuation wrapper only in its description, C/executable filenames, restriction to case 22 and output-summary names. Its state replacement, input/output receipt handling, witness validation and resource policy remain unchanged. The `one_job` body differs only in the launched executable path. Missing explicit state preparation is rejected. The inherited single-coordinator and enabled-assertion assumptions remain; no parallel-safety, power-loss-durability or speed claim is made.

`prepare_engine.py` was read without execution. Its guarded replacements agree with the inspected C diff and wrapper changes. `SpareSupport212.lean` was read as source: its four statements assume an actual exception list bounded by the spare count, distinct forced-variable IDs contained in that list, and the implication from unsupported actual value to exception membership. These generic interfaces correctly express rejection and support filtering. They do not themselves instantiate the C masks or discharge the actual-snake/model interpretation. This reviewer makes no new compiler-acceptance claim.

## SHA-256 pins

Paths are relative to `E:/Snake-in-a-box/milestones/`.

| Source or input | SHA-256 |
|---|---|
| `212-spare-support/scripts/spare_solver.c` | `4c1d8c773075ad6b04c05125b7e5b7fb27b26cdbe9c77e6a9be8d2202700acf0` |
| `212-spare-support/scripts/spare_continue.py` | `15514247092ebcfea8abac7516be09f45f6bb75db0c49edf304e521c94a56d89` |
| `212-spare-support/scripts/prepare_engine.py` | `d4682771674e6334cb78380040273e613065df03a84834fd90c654024f0d79bb` |
| `212-spare-support/lean/SpareSupport212.lean` | `f56de804f455467c89d4ee15c53cbcad3e60aa76a80f6021b36bff96b0ecaf4f` |
| `209-slice-capacity/scripts/history_solver.c` | `5de5aa76686e3cf804da7d6d9dbb2a4202ac44442c5cc1e11fe9a0054cb5f764` |
| `209-slice-capacity/data/square-capacity.json` | `400753eef4c691333e5e03d87239d93fe63ea9f7fc870ac1d742a01afb21bb10` |
| `207-five-history/data/case-6-ordered-from-0-22/model.json` | `1a4d81c600d104347a501cfc9bf82db91a3aa04a6ebfd3ea20fcb1ca283aa95b` |
| `211-subset-capacity/lean/Spare211.lean` | `1bd23b4c4d9592d78d172e36b63cb87dc9d0f31268ffb325450f9ee30b85490c` |
| `211-subset-capacity/lean/Sharing211.lean` | `6f3d0e25dd1c61a940bad64e74fed650af63aa24efd8fa32bdcf881bb3c204b3` |

No source or prior evidence was modified. Only this report was written.
