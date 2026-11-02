# Pre-edit review of the complete manuscript

## Source and review boundary

Read all 3,574 lines of `paper/snake9_research.tex`, including every appendix, displayed catalogue, witness, construction experiment and bibliography entry. The original source is 315,379 bytes with SHA-256 `3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd`. Line references below refer to that exact original. Long reads were divided into bounded chunks; the two truncated portions were reread separately.

Compared current claims with milestones 77–85 READMEs, proof summaries/checkpoints, milestone73's current integration audit, milestone83 comparison and arithmetic receipts, and `handoff/CURRENT_STATUS.md`. The original historical mathematical arguments were read, but their full certificate closures, literature and printed-witness computations were not rerun. No paper edit, Lean invocation, solver run, process intervention, or change to prior evidence was made.

The main required changes concern superseded proof status and the current comparison model. No new construction, optimum, or smaller unconditional upper bound is supported by the reviewed records.

## Priority 1: correct the completed local theorem and pending catalogue

**Affected lines:** 39, 95, 1032–1038, 1053–1070, 1303–1309, 1366, 1371, 1585.

Milestone80 completed case7305. The existing theorem at 1032–1038 must be expanded, rather than retained unchanged as the complete current list:

- Shapes 012031, 012304 and 012314 have five-centre share at least 16.
- Shapes 012310 and 012345 have five-centre share at least 12.
- All statements hold for arbitrary matching snake windows, distinct coordinate labels and reversal, without extra singleton-count conditions. The count ceiling 21 is derived universally when applying the certificate.

For 012310 the direction pattern is `(a,b,c,d,b,a)` with four distinct coordinates. Case7305 passed 465 generated modules and 100 printed theorem audits. The combined catalogue passed 35 audits and now supplies target cases 7300, 7304, 7305 and 7306.

Replace the pending status at line 1063 by checked. Replace line 1070's partial-replay claim with the completed local theorem and exact remaining targets:

| Shape | Target | Case |
|---|---:|---:|
| 012032 | 16 | 7301 |
| 012034 | 20 | 7302 |
| 012301 | 16 | 7303 |
| 012340 | 16 | 7307 |
| 012345 | 16 | 7308 |

The last row remains pending at 16 although its weaker floor 12 is checked. There are **five pending target theorems**, **four completed target theorems**, and **five shapes with some completed count-free bound**. These are different counts. Abstract line 39 currently says four shapes; it should say five if it counts every completed floor.

Evidence: `milestones/80-012310-share-closure/data/checkpoint.json`; `milestones/73-countfree-share-catalogue/data/integration-audit.json`, status `PASS_COMBINED_LOCAL_CATALOGUE_AND_BUDGET`, `case_numbers=[7300,7304,7305,7306]`, remaining `[7301,7302,7303,7307,7308]`.

## Priority 1: replace the current comparison table and its status explanation

**Affected lines:** 1297–1316, with summaries at 39, 95 and 1585.

The mean-480/range-536 row is now historical. The mean-483/range-551 row is the completed-local-share baseline; its 012310 premise has been discharged. The assertion at line 1309 that this row adds an unproved premise is false at the reviewed checkpoint.

Recommended current table:

| Local share assumptions beyond the completed set | Exact mean | Scaled range and denominator | Conditional estimate |
|---|---:|---|---:|
| None | 483 | R=551, d=1 | 157625/669, integer 235 |
| Only 012034 at least 20 | 9259/19 | R=11301, d=19 | 20965613/89059, integer 235 |
| All five pending targets | 496 | R=600, d=1 | 137941/587, integer 234 |

Retain the old 480/536 calculation as a labelled historical row or appendix entry, with the old local subset explicitly identified. A reference to the expanded current theorem cannot continue to label that old subset.

The single-premise row comes from milestone83. Its unscaled potential range is 11301/19; do not print 11301 as though it were in the unscaled weight units. Thus line 1298's statement that all rows have denominator one must change if this row is added. The single additional floor raises 1,043,097 weights over the completed model. It still cannot meet the 234 criterion even at zero range: `111960*19-227*9259=25447>0`.

All three graph calculations remain conditional on the complete actual-snake interpretation and Lean potential assembly. The maintained global interval remains 191 through 235. The existing 496 arithmetic, 32-unit margin and cycle-realization disclaimer at 1311–1316 remain correct.

Evidence: milestone80 checkpoint; `milestones/82-unsaturated-cycle-obstruction/data/graph-audit.json`; `milestones/83-012034-share-certificate/data/comparison-audit.json` and `lean-audit.json`.

## Priority 1: replace the obsolete graph-interface checklist

**Affected lines:** 1253–1295, 1364–1369, 1583–1585. The statement at 1293 that the history converse has no separate Lean check is superseded by milestone77's exact signature equivalence.

The revision should distinguish the following completed components from the remaining assembly:

| Component | Current result | Evidence |
|---|---|---|
| Direction tables | Arbitrary actual eight- and nine-direction windows have exact IDs in the ordered 132/505 tables; source/target IDs and history-shape compatibility are proved | 77: 36 modules, 106 audits |
| Numeric state sequence | Builder selector agrees with the longest-suffix history; actual state and edge count codes have matching consecutive endpoints, m-8 steps and m-7 states | 78: 4 modules, 29 audits |
| Ten interval filters | Every fitting actual window survives both orientations and all three placements, with completed local certificates supplied | 79: 6 modules, 31 audits |
| Forty short filters | All 37 component-cap and three sum rules are connected to actual windows in both orientations and all represented placements, without unresolved local-refutation premises | 81: 8 modules, 66 audits |
| Three history exclusions | Emitted signatures determine their unique eleven-direction words; the proved count floors exclude the encoded caps, including the early-step boundary | 84: 8 modules, 38 audits |
| Reference family | Exact 1,378-key table and retention theorem checked, conditional on `AllRefuted6K235` and `AllRefuted236` | 85: 27 modules, 103 audits |

For the reference union, record `1287+732-641=1378`, with all chosen representatives directly present in a source list and 2,678 distinct oriented pairs. The 235 and 236 closed refutations have preserved historical audits. Their matching closed objects have not been imported into the current environment; compiling key-data modules does not discharge their propositions. Line 1263's broad sentence about no unresolved additional count exclusion should be replaced by this precise distinction between historical local certificates and the current conditional interface.

The three history signatures and count positions can be printed compactly:

| Signature | Eleven-word starting at s=r-2 | Proved count floor | Six-code digit |
|---|---|---|---:|
| (139,353,177) | 01230432543 | alpha(s+10)>=3 | 5 |
| (460,350,180) | 01234532013 | alpha(s+8)>=3 | 3 |
| (460,353,177) | 01234532053 | alpha(s+10)>=3 | 5 |

They cannot emit at r=0 or r=1. The uniqueness proof covers all 81 continuations of each fixed nine-prefix; the separate complete Python enumeration has 11,162 induced canonical eleven-words. These facts close the three exclusion signatures only. The ambiguity warning for other three-ID share signatures at 1295 and 1650–1658 remains necessary.

Replace the remaining-work list with: supply the two closed reference premises in the current environment; prove the exact retained-array index/membership; cover every compatible realization of every credited history and interpret its share/count conditions on the final five centres; replay the complete potential and telescope; complete the five target local shares. The existence of a consistent encoded state sequence is already proved; its membership in the retained graph is still open.

The separate Python filter comparisons and their large pair counts are evidence for isolated filters, not counts of newly removed full-graph edges and not Lean proofs of Python execution. This distinction should remain explicit.

## Priority 2: add the newer obstruction and single-target limitations

**Insertion point:** after current comparison or alongside 1318–1358.

Milestone82 adds a useful theorem about the fixed completed-share comparison graph: a four-edge cycle has weights `(252,480,600,600)` and six count symbols below six on every edge. Its total is 1932 and mean 483. Any nonnegative edge bonus that vanishes whenever all six symbols are below six preserves that exact minimum mean. The existing potential supplies the lower bound and the unchanged cycle supplies the upper bound.

The fixed budget then cannot establish 234, since any potential slope p/d satisfies `p<=483d`, giving `227p-R<=109641d<111960d` for nonnegative R. The deficit is already 2319d at zero range. Six Lean audits check the literal and algebraic statements; array membership and all-edge inequalities are separately checked in Python. This establishes a finite-model obstruction, with no actual-snake realization asserted.

The conditional floors for 012034 and 012340 would increase this particular cycle's mean to 497. That is a witness-only sensitivity calculation; it is not the new whole-graph minimum. Milestone83's whole-graph single-premise mean 9259/19 demonstrates why those distinctions matter.

The 60-second test of 012034 floor 32 returned UNKNOWN with no witness. It supplies neither a counterexample nor a theorem. If retained, it belongs in a short diagnostic note, not among established bounds.

## Priority 2: correct wording while retaining valid older results

- **Lines 1342–1358:** all six saved weakening experiments remain valid numerical results. Keep the six-row table if retaining its historical scope. The 012310 row now deliberately removes an already proved floor; it is no longer one of the unresolved local targets. Line 1371's phrase “six pending floors” must become “five pending floors” or refer explicitly to the six historical weakenings. Do not globally replace every occurrence of six.
- **Line 1362:** “an equivalent sufficient numerical criterion” is unsupported if it claims equivalence with the eighteen-empty-square condition. Both are sufficient routes, but no equivalence between them is proved. Use “the potential criterion of Corollary ...” or “another sufficient criterion”.
- **Lines 39, 73–98, 224–227, 1578–1585:** preserve the contributor-based 235 result with the evidence boundary visible near the main claim. The checked contributor closure is historical evidence; the new local interface has explicit premises. The absence of current imported closure objects neither supplies a fresh independent proof nor invalidates the recorded contributor theorem. Avoid implying that milestone85 independently closed it.
- **Lines 1398–1410 and older appendices:** the six-centre four-count conjecture and its 30 unreplayed exclusions are a different case family. Milestone80's 012310 completion does not discharge that conjecture. Likewise, earlier restricted models, local forests, solver UNKNOWN/INFEASIBLE reports and historical radius-three routes keep their original scopes.
- **Lines 1429–1587 and 2785–3321:** the value 196 is already labelled an extrapolation without a witness or optimum proof. The competing model predicting 195 and the next-length criterion are sound scope controls. Preserve them. The disconnected 197-vertex construction and its 196 edges are not a 196-edge snake; the manuscript correctly says so. No reviewed later record changes the lower bound 191 or supplies a matching upper bound.

## Organization and citations

The present paper has a coherent route from square census to local shares and global accounting, but the current-status discussion is duplicated in the abstract, principal-results table, current-model section, remaining-work list and conclusion. Rewrite those five locations from one current status table to prevent contradictions.

A clearer core order is: precise global result and provenance; square/count identities; share geometry and local theorems; current completed-versus-pending catalogue; accounting and conditional criterion; exact graph interpretation with a completed/pending dependency table; finite comparison and obstructions; remaining mathematical requirements. Keep old finite models and construction searches in their existing appendices, explicitly dated or labelled historical. “Current complete charge model” at 1253 can become “Current finite comparison graph and its interpretation”, avoiding ambiguity between complete finite enumeration and a completed global proof.

Bibliography lines 3553–3567 currently stop the relevant local/interface references at milestones70–75. Add pinned references for the 7305 completion and milestones77–85; the old `countfreearchive` revision predates the now-completed case. Preserve older pinned citations for historical claims. Do not silently refresh the contributor's separate conditional234 production status at 1373/3569–3571 without new evidence. The existing literature citations were not refreshed in this review, as requested.

Preserve the three authors and existing `hypersetup` settings at lines 11–18 and 34. Updating a catalogue theorem or replacing an obsolete comparison row is a substantive correction; a preservation check should not force those stale statements to survive verbatim. Witness strings, explicit old catalogues and valid historical results can remain intact.

## Verification snapshot and remaining uncertainty

Current successful summary statuses inspected were: 77 `PASS_DIRECTION_AND_HISTORY_SHAPE_INTERFACES`; 78 `PASS_NUMERIC_HISTORY_AND_ENCODED_STATE_SEQUENCE`; 79 `PASS_ENCODED_GUARDS_AND_TEN_INTERVAL_RETENTION`; 80 `PASS_012310_SHARE_CLOSURE_AND_MODEL_COMPARISON`; 81 `PASS_FORTY_SHORT_RULE_RETENTION`; 82 `PASS_UNSATURATED_CYCLE_OBSTRUCTION`; 84 `PASS_THREE_HISTORY_EXCLUSION_RETENTION`; 85 `PASS_REFERENCE_UNION_CONDITIONAL_RETENTION`.

Milestone83 remains `PARTIAL_SHARE20_SEMANTICS_AND_EXACT_CONDITIONAL_COMPARISON`. At inspection, `milestones/73-countfree-share-catalogue/cases/case7302/data/proof-audit.json` did not exist. Partial successful modules and the generated geometry source cannot support a completed share-20 claim. The live driver was not inspected or disturbed. Refresh only its final success gate before freezing the revised paper, since progress can change during revision.

Key summary hashes: milestone80 checkpoint `e762772cc86c7bb5952e75801aa1da0b62637a72ddba62e9a707805860421984`; milestone83 comparison `8d3cedcb25436fab7257d5cf36f2eb2e07d7f3baf52fab3aaaba803dcf4b385b`; milestone84 proof summary `43eabfa2f1e0829b60e48a0851a1ce936bfa96143490f55ef2e6a73a07a88905`; milestone85 proof summary `c486f9503e901d7164337a06bc58842df799d9a81f6d8e57a04620d5ee80ec7b`.

This review does not certify every older printed proof or establish external novelty. It identifies the required source-grounded status corrections and scope limits after reading the complete original. The revision still needs its own source consistency checks and compiler result; a successful source edit alone supplies no PDF or layout verification.
