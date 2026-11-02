# Scope of this archived ledger

Entries below are chronological development history. This archived section records the development through the 245 bound. The maintained repository currently records 235; later checkpoints are listed in the milestone index. Paths under dated research directories refer to local material, not files required for this PR. Maintained sources and reproduction instructions are in `work/spectral/`.

# Research ledger — 15 October 2026

## Objective and status

Determine the exact maximum **edge** length of an induced path in Q9. Completion requires an explicit length-L snake and an unconditional exclusion of length L+1, both compiled in Lean with audited dependencies. **Unresolved.** No preferred value of L is assumed.

Base repository: `hironaka-iori/Snake-in-the-box-in-9`, commit `37ec31e9c5667bf3cc2795e4cbec89537ebe9af6`. Cloned using the user's existing local Git access into the requested folder. Working branch: `research/2026-10-15-autonomous-audit`. Original tracked proof sources are preserved. Documentation and the authoritative manuscript are being updated from backed-up originals to record the new verified bound.

## Inherited evidence, awaiting fresh proof reproduction

- Repository interval: 191 <= a(9) <= 254. Historical Lean logs support the stated proofs; new local compilation is tracked separately below.
- General prefix theorem already exists in `work/final_lean/OptimalityTarget.lean`; it uses precisely `Snake9.Snake` from the construction theorem.
- Endpoint-blocked does not mean globally longest. The repository contains a 93-edge counterexample.
- The 131-example bank is not a complete classification. Orland et al. arXiv:2607.15270v3 explicitly labels it a discovered bank, not a census.
- The 196 extrapolation has neither a witness nor an exclusion of 197. It receives no privileged search status.
- Fixed-prefix searches, fixed-seed layer searches, and two-deletion neighborhoods have restricted scopes. UNKNOWN yields no exclusion. Saved restricted solver exclusions have no Lean certificates.

## Parallel work and ownership

- `work/research_20261015/proof/`: fresh Lean/toolchain and pinned mathlib reproduction, definition/dependency audit.
- `work/research_20261015/construction/`: independent bank/witness validation, materially different multi-cut construction search.
- `work/research_20261015/upper_bounds/`: aggregate singleton-square restrictions with counterexample testing.
- `work/research_20261015/audit/`: primary-source/dataset refresh and global encoding/symmetry audit.

## Fresh findings

1. The construction worker independently ran the repository's read-only witness validator with bundled Python 3.12. All four witnesses and 131 bank snakes passed. This is executable checking, not fresh Lean reproduction.
2. Inspected README, COLLABORATION, manuscript, core snake definition, next-length theorem, exact-search model, local-square model and saved search summaries.
3. Current primary sources opened: arXiv:2607.15270v3; arXiv:2609.27483v1; Math-AI-Caltech public data repository; Lukito–van Zanten (2001) publisher PDF. Do not transfer cycle upper bounds to paths without proving a bridge.

## Search record requirements

Every new search records model/code hash, source data, dimension, target, exact fixed restrictions, symmetry justification, solver/version, seed, workers, limits, status, and elapsed time. A feasible result needs an independent distinctness and all-pairs adjacency check. An infeasible result needs an encoding audit and proof certificate before any formally verified exclusion is claimed.

## Next actions

Complete fresh proof compilation; refresh the public subset with hashes; test and prove the proposed low-singleton/endpoint restriction; run construction search beyond previously exhausted neighborhoods; independently audit global model symmetry with exhaustive small-cube controls. Maintain this ledger and per-worker notes as results arrive.

## Live update: proof reproduction and new candidate bound

- Fresh Lean 4.19.0 core build (all15 modules) and both pinned-mathlib bounds254/255 succeeded. Logs and source hashes live under `work/research_20261015/proof/logs/`. Only `propext`, `Classical.choice`, `Quot.sound` occur in audited theorem dependencies. The witness itself uses `propext` only.
- Public archive refresh matches the inherited SHA256 and all 131 ordered transitions exactly;2,402,016 unordered pairs independently checked. The same archive contains1,042 inequivalent190-edge snakes, now available to construction search.
- New written lemma: adjacent internal vertices cannot both have singleton-square count1. Its arm restriction is Lean checked. Two final geometric cases force too many endpoints or a selected8-cycle. Full geometry integration is ongoing. A conditional Lean theorem already derives251 edges from this local lemma, but **do not call251 an unconditional Lean bound until the geometric premise is discharged**.
- Root compiled `CycleStructure.lean`, `SingletonAlphaBridge.lean`, `NormalizeAdjacentSingletons.lean`: six/eight-cycle exclusion; exact alpha=1 to unique missing pair; translation invariance; normalization from arbitrary adjacent internal path indices. Standard foundations only. Proof worker owns final normalized contradiction.
- Built-in Lean4.19 `bv_decide`/`bv_check` route was inspected and invokes `Lean.ofReduceBool`; it is not being used to evade the kernel-checking requirement. All new compiled lemmas use ordinary proof terms/kernel `decide`.
- Independent global-model audit passed35 exhaustive Q1–Q4 controls. Its positive-length/n>=2 symmetry coverage is justified analytically. Degenerate n=1/target>=2 symmetry and target0 issues are recorded as out-of-scope API limitations.
- Exhaustive Q4 local-forest incidence relaxation (65,536 masks;14,911 forests;84 statistic vectors) yields no improvement over254. Saved as a failed strategy to avoid repetition.
- Stronger adjacent-alpha probes: (1,2) and(1,3) returned INFEASIBLE under the full connected-path encoding; these are solver evidence only. A(2,2) counterexample of 127 edges was independently checked. Upper worker found a(1,5) witness and solver minimum5 under justified local normalization; not yet a theorem.
- Construction rotation/short-bridge closure exhausted330 labelled paths, all belonging to the original131 isometry classes. No record improvement. Multi-cut repairs, diverse190 seeds, and targeted endpoint-blocker repairs are recorded in the construction ledger; restricted INFEASIBLE and UNKNOWN remain distinct.

## Completed unconditional strengthening: 191 <= a(9) <= 251

Both normalized geometric cases, translation/normalization from arbitrary adjacent internal vertices, and the final global wrapper compiled successfully under Lean 4.19.0 with the pinned mathlib. The final theorem `Snake9.verified_interval_191_251` uses only `propext`, `Classical.choice`, and `Quot.sound`. An independently written wrapper compiled to the same interval. The earlier warning that 251 was conditional is now discharged.

The authoritative new sources are in `work/spectral/stronger/`. Dated research `.lean` files are frozen development snapshots; future maintenance belongs in the authoritative directory. The portable `verify_strengthened.py` completed a fresh source-only core build and every strengthening module successfully, with final transitive audits. Saved evidence: `outputs/strengthened-reproduction-manifest.json` and `outputs/strengthened-reproduction.log`. The manuscript, README, and collaborator handoff are synchronized; author Iori Hironaka is preserved. The updated manuscript compiled successfully in the desktop LaTeX compiler. No exact optimum or novelty priority is claimed.

The next mathematical target is excluding adjacent counts (1,2). A complete written proof passed independent review and finite case-bookkeeping checks; geometric formalization is ongoing. The conditional aggregate theorem `upper_248_of_no_adjacent_one_two` compiled, but its new premise is not yet discharged, so 248 is not yet a verified bound. Construction work produced five new-to-our-input 97-edge Q8 classes; all ten 94-edge partner searches returned UNKNOWN at 20 seconds. Diverse fixed-layer searches now use known shorter compatible partners as unfixed hints. No 192-edge Q9 witness has been obtained.

## Completed unconditional strengthening: 191 <= a(9) <= 248

The remaining premise above has now been discharged. `UpperBound248.lean` compiled successfully, including the normalized configuration exclusion, exclusion for arbitrary adjacent internal vertices, global `upper_bound_248`, and `verified_interval_191_248`. All four transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The proof uses the same original snake definition and lower-bound witness. The exact optimum remains unresolved.

Twelve additional modules are integrated into `work/spectral/stronger/`, bringing the maintained strengthening project to27 modules. The portable driver is undergoing a new source-only rebuild of the full 248 proof. The prior successful 251 build is preserved separately as `outputs/strengthened-251-reproduction-manifest.json` and `outputs/strengthened-251-reproduction.log`. README and handoff now report248; the authoritative manuscript is being updated from a backup of its251 version.

Further probes found no path with three consecutive internal alpha2 vertices in either of the two exhaustive five-vertex window shapes; both returned INFEASIBLE. The same two shapes also excluded internal alpha1 vertices at distance two with the intervening count unrestricted. These remain solver evidence, with no formal certification. Human investigation of the distance-two restriction is underway. The direct square-indicator model passed a positive (2,2) control with an independently verified110-edge path.

## Completed unconditional strengthening: 191 <= a(9) <= 247

`UpperBound247.lean` compiled the endpoint lower bound four and the global upper bound247 using only `propext`, `Classical.choice`, and `Quot.sound`. The finite missing-pair classification and both geometric cases are discharged. The aggregate estimate is `4*m+10 <= 2*T`; there is no new solver premise. `EndpointFourWitness.lean` independently checks a120-edge example with exactly four singleton squares at its first endpoint, using only `propext`. Its four coordinate pairs are {1,5}, {2,7}, {3,8}, {4,6}.

The maintained project now has33 strengthening modules. The fresh248 source-only reproduction succeeded and is preserved as `outputs/strengthened-248-reproduction-manifest.json` and its log. The fresh247 reproduction also succeeded:36 steps including the core, incidence theorem, all33 strengthening modules, and final audits. Every recorded source hash matches the maintained files. Its manifest and combined log are saved both under `outputs/strengthened-reproduction-*` and the versioned247 filenames. README, collaborator handoff, and manuscript report247; manuscript author Iori Hironaka is preserved and desktop LaTeX compilation succeeded. Earlier ledger statements are historical checkpoints, not competing current bounds.

Research continues on adjacent counts(1,3), distance-two count-one vertices, and runs of three count-two vertices. Construction searches have not produced192 edges. A deliberately shortened188-edge class regrew to191 but returned to an existing isometry class. A new overlay search permits multiple crossings between two Q8 paths, beyond the previously exhausted single-join families. The exact optimum remains unresolved.

## Adjacent (1,3) exclusion and triple-two research

The adjacent (1,3) exclusion is now unconditional for arbitrary internal path indices. Its eight additional maintained modules bring the strengthening project to41. A complete fresh source-only build succeeded at2026-10-15T07:44:23Z; all recorded source hashes were rechecked against current files. The manifest and combined compiler output are saved under both `outputs/strengthened-reproduction-*` and `outputs/strengthened-247-one-three-reproduction-*`. Only the three standard foundations occur in the audited dependencies. The manuscript includes the human proof and compiles successfully. This local exclusion alone does not improve247.

The repeated-coordinate five-vertex window with three consecutive internal alpha2 vertices is excluded in compiled Lean, including the outer matching classification, middle contradiction, and normalization. These new development modules have not yet been integrated into the maintained driver. The distinct-coordinate window remains open; its outer-family classification and middle geometry are being formalized separately. Exploratory propagation/DPLL closed366 symmetry representatives of the both-exception case, but its computational exclusions are not yet kernel certificates and are not used as theorem premises. The exact optimum remains unresolved and the verified numerical interval remains191--247.

## Triple-two classification: only unequal ordinary outer remainders remain

All exceptional-count cases, the common-hole case, the star/star case, both mixed star/ordinary orientations, and the equal ordinary-pair case have now been excluded by compiled Lean proof terms. The final development theorem `DistinctOuterConfig.remaining_unequal_ordinary_case` in `proof/ThreeTwosRemainingUnequal.lean` reduces any still-possible distinct-coordinate triple-two window to two distinct 2-element sets A,B in the five ordinary coordinates, with outer missing families `{bd,A}` and `{ac,B}`. These new modules use only the standard three foundations and remain development sources pending the next maintained-project integration and fresh source-only build.

The mixed-case proof is symbolic: three clean rows force a middle edge to touch them; the two-edge budget then makes every middle-isolated row supply an endpoint; each ordinary middle missing edge supplies another endpoint, possibly at its associated row. The resource families are disjoint, and two missing edges on five coordinates demand at least three endpoints. No exploratory solver result is a premise. `MixedOuterExclusion.lean` completes this argument. `EqualOuterPairExclusion.lean` independently closes A=B.

The remaining unequal A,B cases are being separated into disjoint and shared-coordinate pairs. Generic row geometry and ordinary-pair endpoint lemmas have compiled in `audit/OrdinaryRowGeometry.lean`, `OrdinaryIsolatedGeometry.lean`, `OrdinaryIsolatedOneSide.lean`, and `OrdinaryPairEndpoints.lean`. These are intermediate lemmas, not yet the final exclusion of all triple-two windows.

The global aggregation step has been proved separately and is explicitly conditional. `audit/AlphaRunPotential.lean` proves `7*n+5 <= 3*sum(alpha)` for a positive sequence whose ends are at least4, whose count-one entries have neighbors at least4, and which has no three consecutive twos. A five-state potential handles the valid pattern1,4,1, which invalidates a naive three-term lower bound. `audit/Aggregate245Conditional.lean` compiles `upper_245_of_no_three_twos`: once the remaining local exclusion is supplied, the same incidence identity gives at most245 edges. **245 is not yet an unconditional bound. The verified interval remains191--247; the exact optimum remains unresolved.**

Construction work has moved beyond fixed input banks to joint variable Q8 layers. The model retains a fully checked191-edge positive control; several bounded runs timed out, and degree-only relaxations produced disconnected cycles which were explicitly rejected or cut. No192-edge construction has been obtained. Restricted finite neighborhood exclusions and timeouts remain distinct from an unrestricted impossibility theorem; details and scopes are in the construction ledger and `construction/JOINT_LAYER_METHOD.md`.

### Subsequent local milestone: disjoint ordinary remainders excluded

`OrdinaryEndpointCount.lean` now proves that the combined distinct endpoint resources of an unequal ordinary outer pair have cardinality at most2. `DisjointOrdinaryDemand.lean` proves at least3 when those outer pairs are disjoint, and `OrdinaryDisjointExclusion.lean` combines them. All compile with standard foundations only. The two-ordinary-middle-edge subcase is proved symbolically in `audit/OrdinaryTwoEdgeDemand.lean`: a failed hole endpoint criterion forces a two-edge wedge, which leaves two isolated coordinates and makes the other hole an endpoint. No solver exclusion or unchecked computation is used.

`NormalizeSharedThreeTwos.lean` therefore reduces every remaining triple-two window to outer pairs A={e,x}, B={e,y}. In that shared-coordinate case, `SharedOuterSwitch.lean` closes the difficult middle family F={{e,k},{x,y}} for clean k by a present/absent central-square argument. Several other exact families are compiled, including central F={{c,d},{c,e}} and its mirror, root's `SharedMissingRightFamilies.lean` (F={{e,y},S}, S contained in {c,d,e,x}, S different from {c,d} and {c,e}), and `SharedCrossStars.lean` (F={{c,x},{d,y}}). Remaining shared families and the complete finite coverage proof are still being completed. The maintained numerical bound remains247 until the full no-three-twos theorem and its global wrapper are complete and freshly reproduced.


## Completed theorem: unconditional interval 191 <= a(9) <= 245

The complete arbitrary-path no-three-consecutive-twos theorem and unconditional `upper_bound_245` / `verified_interval_191_245` compiled successfully. All final transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`; an independent import audit also passed. Every shared-coordinate residual family is now excluded. The final symbolic classification covers all441 ordered choices of two edges among21 coordinate pairs; arbitrary-coordinate injectivity and coverage are proved, and equal-edge choices are rejected. The final ordinary-hole/xy branches are in `SharedOrdinaryFork.lean`. No solver premise or unchecked computation enters these proofs.

The maintained strengthening project now contains148 modules (107 new beyond the previous41), with the same original core snake definition and191-edge witness. The dependency closure was independently reconstructed and agreed. Maintained `CoordinateCycle.lean` takes precedence over its historical development copy; only proof tactics differ. The strengthened reproduction driver includes all148 modules and final no222/245 audits. A fresh source-only rebuild is running in `work/spectral/.verification/strengthened-l_md7bys/`. The saved `outputs/strengthened-reproduction-*` files still describe the previous successful247 checkpoint until the new run completes.

README, handoff and manuscript now state245 and distinguish completed theorem compilation from the ongoing clean reproduction. Pre-update files are backed up in `audit/backups/pre-245/`. The manuscript retains Iori Hironaka, gives the complete potential argument and numerical deduction, and explicitly labels its longer geometric classification account as a summary of the full formal proof. Exact optimality remains unresolved; no192-edge construction has been found.

Further research is testing whether the surviving count pattern223 or related consecutive patterns can occur. Excluding adjacent(1,4) alone cannot improve the present aggregate bound, because periodic223 still attains average7/3 under all those restrictions. Construction research also continues beyond fixed-layer and small-neighborhood families.


### Work after the 245 theorem

The updated authoritative manuscript compiled successfully in the desktop compiler. The fresh148-module proof reproduction continues without a reported failure. `Alpha223Potential.lean` and `Aggregate244Conditional.lean` compile a conditional next target: excluding internal counts223, together with the proved no222 result, gives `2*T >= 5*v+3` and at most244 edges. The no223 premise is explicitly retained. It is not a new unconditional upper bound.

An independent Fourier/distance-distribution relaxation was tested in `audit/probe_distance_distribution.py`. Its ordered distance-two identity `y2=23*v+10-T` and other necessary constraints passed all 131 known-bank controls. The relaxation admits an exactly checked rational vector at246 vertices, so these aggregate constraints do not improve245. That vector is not a snake construction. A second continuous relaxation of the local223 degree model also remains feasible with all square cuts, the known global size bound and all ten sampled cycle cuts; it provides no short linear contradiction. Scripts/results are preserved rather than treated as exclusions.

Root has compiled generic counted outer-family geometry and repeated-window resource counting in `CountedOuterConfig.lean`, `RepeatedResourceData.lean`, and `Repeated23HoleFree.lean`. For outer counts2 and3, at most one common row hole is possible. With no common hole, the left missing family is a two-edge matching contained in the three-edge right family, and the two unused coordinates force both endpoints. These are development lemmas only; the repeated223 exclusion is not yet complete. All successful theorem audits use only standard foundations.


### Fresh 245 reproduction completed

The source-only build in `strengthened-l_md7bys` completed successfully at 2026-10-15T10:44:35.144919+00:00. All151 steps passed: the original core, incidence theorem,148 strengthening modules, and final transitive audits. All167 recorded source hashes match the maintained files. The manifest and combined log are saved as both `outputs/strengthened-reproduction-*` and `outputs/strengthened-245-reproduction-*`. The general prefix theorem and unchanged191 witness were included in the final audit. README, handoff, spectral instructions, and manuscript now record this successful reproduction. Earlier running-status paragraphs above are historical. The exact optimum remains unresolved.


## 23 October 2026: distance-three pair inequalities and six-count classification

Milestone32 now has 18 passed Lean audits: arbitrary-snake normalization, 34-case coverage, conditional no-six-four and density implications, plus four individual numerical refutations. All 34 native proofs are generated; only cases0,1,14,22 have completed Lean replay. The six-count-four statement remains a conjecture. A conditional graph test removes96 transitions and changes the saved witness mean287/60 to1739/360; lower mean119/29 survives.

Milestone33 develops the geometric reason behind small cases22 and25. For transition patterns(a,b,c,d,e,b,a) and(a,b,c,d,e,b,f), the first and sixth internal singleton counts sum to at least10 and9, respectively. All named coordinates are distinct. Six forced opposite corners and four or three disjoint induced six-cycles explain the bound. Nine Lean audits, including coordinate normalization, passed. The cores have246/194 clauses and3405/1470 hints. Independent checks verified956 pattern occurrences across all 131 bank paths; observed minima16/19 do not imply stronger universal bounds.

The two proved inequalities give the same recorded witness-cycle improvement as the unfinished six-centre conjecture, while the lower-table cycle remains119/29. Selective count memory increases the diagnostic graph to70,416 states. Exact saved-cycle checks and source/proof archives are retained; there is no complete minimum-mean certificate or new global bound. The next route is a broader disjoint-cycle pair inequality or sharper empty-square shares on surviving mixed-count cycles. The paper and open editor mirror are synchronized. The built-in preview again failed before TeX because of the Windows split-writable-root sandbox restriction.


## 23 October 2026: both distance-three constants are sharp

Milestone34 first attained sums10 and9 in local radius-four forests with18 and19 components. Separate full-cube searches produced complete143-edge and138-edge snakes attaining the bounds with pair counts(6,4) and(5,4). Twelve Lean audits verify the paths, direction windows, counts and the deductions that neither universal constant can increase. The counts occur at indices68/73 and71/76, respectively. The paper includes complete transition sequences. Independent enumeration gives pair shares48+29 and25+17, with charges317 and258; these share values are not Lean-certified in this checkpoint.

Two bounded searches combining equality with at least193 vertices returned UNKNOWN. The maximum-length goal remains unresolved and the integrated191--238 interval is unchanged. The next target is a share bonus of at least12 for the second pattern at count sum9, which would give pair charge228. This is an unproved target requiring local verification and eventual overlap/frequency accounting.

## 23 October 2026: three-square share bonus

Milestone35 proves pair share at least 12 for the six-distinct-coordinate pattern (a,b,c,d,e,b,f), without an equality assumption. Together with milestone33 this yields pair charge at least 228. Three forced empty squares give contributions 2,4,4,2. The 115-clause core uses only selected-window and degree clauses, with 281 LRAT hints. Thirteen Lean audits include the geometric share bridge pinned to d4936d72, arbitrary coordinate labels, and occurrence accounting: N qualifying starts imply total share at least 6N. Independent exact-quotient and tagged models accept the 138-edge witness with shares 25,17.

No global frequency lower bound or integration with overlapping window shares is proved. The repository interval remains 191 to 238 edges. GitHub branch heads were refreshed and unchanged. The paper mirror is synchronized; the built-in preview compiler failed before TeX due to the Windows split-root restriction.

## 23 October 2026: mixed-count overlap exclusions

Milestone36 completes two geometric exclusions with six Lean audits, 1973 total core clauses and 68743 LRAT hints. The six-step witness cycle has six numerical excluded phases. The 29-step lower cycle has 28 numerical exclusions and one UNKNOWN. Two phases are theorems. Selective count history adds216 states and passes279936 update comparisons. The replacement witness mean is29/6; the lower mean remains119/29. No global bound changes. The next user-requested task is a complete logical rewrite of the existing manuscript after this research checkpoint.

## 24 October 2026: complete logical manuscript revision

Milestone37 rewrites the existing paper around its proof dependencies. A direct square census precedes the necessary local conditions; all175 exclusions are printed; the44064-state potential is followed by its full summation and endpoint deduction of238. Sharp pair counts, empty shares, overlap exclusions, conditional charge targets, construction criteria, and the196 conjecture have separate logical roles. Detailed classifications and experiments remain in appendices.

All72 prior labels and all76 prior mathematical statements are retained, with four statements restated without changing their content; four explanatory statements make the direct proof explicit. The complete witness appendix is unchanged. Five new Lean arithmetic checks use only propext and Quot.sound. An independent finite enumeration verifies1026432 candidate transitions, including700433 permitted ones, and the full175-row catalogue. Authors, preamble, hyperlink settings and editor synchronization pass source checks. The built-in compiler failed before TeX due to the Windows split-root runner configuration; no PDF layout verification is claimed.

GitHub refresh finds671d21f5 on the collaborator's Keller branch, explicitly incomplete bridge infrastructure toward235. It is recorded without importing an unproved bound. The integrated interval remains191--238 and the exact optimum is unresolved.

## 24 October 2026: asymmetric distance-four singleton restrictions

Milestone38 generalizes the smaller mixed-count exclusion. For transition pattern (a,b,c,d,e,c,a,d), with distinct labels, counts X,Y at the first and seventh internal vertices satisfy X>=2, X<=2 implies Y>=4, and Y<=1 implies X>=9. Three new cores have 14, 1464 and 1152 clauses, with 23, 73621 and 23622 LRAT hints. Seventeen Lean audits include arbitrary-coordinate interpretations, the inequalities X+Y>=5, 2X+Y>=8, X+6Y>=15, and excess/occurrence accounting. No restrictions remain on the intervening counts.

Independent checks validate 17 local forests. Pairs (2,4), (3,2), (9,1) occur in forests with 153/18, 146/12, 162/20 vertices/components, respectively. These do not prove sharpness for full snakes. The saved lower cycle contains a reversed occurrence with pair (3,3); the saved witness cycle has none, so both survive. A distant singleton forces at least three excess counts above six, yielding a possible charge correction of72 per oriented occurrence, subject to shared overlap accounting. No new global bound or construction is obtained. The paper includes the theorem, its proof architecture, and the quantitative accounting consequence; authors and hyperlink settings are preserved.

## 24 October 2026: integrate the audited 236 theorem

Reviewed contributor commit 7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b. Its final theorem discharges all 732 radius-four window exclusions and its saved Linux audit lists only standard axioms. Milestone39 pins 12 proof interfaces and receipts plus all 732 keys. It does not claim a fresh local rebuild of the complete replay closure. Independent enumeration passed all 1,026,432 candidate transitions, with 611,613 permitted, and four new Lean arithmetic audits passed. The actual potential maximum is 48; the checked summation uses the valid weaker bound63 and hence boundary291. The paper now explains this choice and proves the 236 conclusion with all endpoint terms explicit. Its principal interval is 191 <= a(9) <= 236. Authors, hyperlink settings, prior statements except the strengthened principal theorem, and witness appendix are preserved. The existing editor is synchronized; preview preparation still fails before TeX in the Windows runner.

## 24 October 2026: intervening-count restrictions

The preceding round made verified progress by incorporating the audited 236 theorem and its full manuscript argument. This round tests the surviving lower-table cycle, rather than assuming its compatibility from pair inequalities. Its reversed phase 18 has directions 01234203 and counts (3,4,4,5,5,3,3). Two new universal local implications now exclude that occurrence: first and seventh counts at most 3 force both third and sixth counts at least 5. The two cores have 2708/1419 clauses and 1141561/86400 LRAT hints. Both refutations, geometric interpretations, and arbitrary coordinate normalization passed eight Lean audits. Twenty-three local forests have independent checks. The degree-and-endpoint relaxation admits a 142-vertex configuration with three cycles, showing why cycle exclusions matter to this local proof. The second certificate's four cycle cuts are translates of one induced ten-cycle. Joint thresholds 12 and 24 have numerical support and local attainments but remain unproved. No new global bound or minimum cycle mean is claimed; the paper's interval remains 191..236. The paper and existing editor were updated with authors and settings preserved. The desktop editor compiler succeeded on the current source; the prior runner error did not recur. Rendered pages have not been visually inspected.

## 24 October 2026: joint intervening sum and overlap accounting

The preceding goal round made progress by proving both individual thresholds 5, compiling the revised paper, and pushing the checkpoint. Milestone 41 proves the stronger joint threshold 12 under the same two distant-count caps. A generic concatenated-counter identity preserves multiplicities; the 4097-clause core with 1401 active variables was replayed using 5222602 hints in 174 segments and 29 check modules. All 208 recorded build modules succeeded. Ten final dependency audits cover the counter, clause interpretation, arbitrary-snake theorem, and excess accounting. A qualifying truncated sum at most 11 forces one count-excess unit, giving a conditional charge contribution of 12 per occurrence after multiplicity-two accounting. This shares the existing excess budget. Independent checks of all 131 bank paths find 1442 oriented pattern occurrences and zero qualifying low-count occurrences, so there is no frequency claim. The local forest attaining 12 was independently rechecked. The five-centre sum 24 remains numerical. The paper and existing editor source were updated and compiled successfully; visual inspection of every rendered page remains undone. The global interval remains 191..236.


## Milestone 62: vertex-split empty-square charge

Eight arbitrary-snake geometric share bounds and three finite potential certificates passed 12 Lean modules and 88 axiom audits. The eleven-transition restricted mean is now 2483/600, up by 1/240. The global interval remains 191..235; no optimum or new global upper bound is claimed. Count-conditioned and floating LP candidates are preserved separately and excluded from checked weights. Research round 6 of 10 after manuscript revision 56; full rewrite scheduled for 66. See milestones/62-count-conditioned-share/README.md for proof, data and scope.


## Milestone 63: longer-window vertex splits

Thirty-eight arbitrary-snake share bounds and the restricted-family mean 4973/1200 passed 39 Lean modules and 348 axiom audits. Independent coverage checked 94,432 split candidates on 214 shapes. The all-vertex and neighbourhood searches have identical optima under the fixed degree-forcing rule. The integer-weight threshold gap remains 73/30, so the global interval stays 191..235. Unproved pilots favour complete neighbour choices over one extra binary split; neither pilot is part of the checked graph. Research round 7 of 10 since manuscript revision 56; next full rewrite at 66.


## Milestone 64: complete neighbour-choice share bounds

The full replay passed 36 modules and 216 theorem-dependency audits. All 34 local arbitrary-snake bounds and the exact restricted minimum 1991/480 are checked. Independent reconstruction covers 11,554 configurations and 2,044 reduced certificates. The remaining zero-range threshold gap is 119/60; the global interval remains 191..235. Count-conditioned pilots remain unproved. Research round 8 of 10 since manuscript revision 56; next full rewrite at 66.


## Milestone 65: count saturation and empty-square shares

Nine arbitrary-snake share improvements and a direct terminal count lower bound three passed 17 Lean modules and 104 audits. All 479 compact branch certificates and 217 deduction steps pass independent reconstruction. Shares alone give the restricted minimum 9961/2400. The direct exclusion of transition 24 removes every cycle of the saved family, whose longest remaining walk is 19. No global upper bound follows from this restricted graph. GitHub refresh to contributor 838303ae confirms unfinished certificates and shards in the proposed 234 chain; the recorded upper bound stays 235. Research round 9 of 10 since revision 56; integrate the restriction into the complete model and rewrite the paper at milestone 66.


## Milestone 66: complete-model integration and manuscript revision

The checked terminal-count restriction raises the complete recorded model's integer minimum from 9891/20 to **18823/38** (normalized **18823/4560**). Independent verification covers all 13,173,896 transitions of the final history model. Eight share patterns strengthen 175,293 transitions; three count restrictions exclude 17,161 lifted transitions. The complete remaining minimum-mean family has **70 states and 99 transitions**. Two new arbitrary-snake count bounds and six arithmetic deductions passed 3 Lean modules and 16 audits. The conditional integer estimate remains 235, and the contributor-checked global interval remains **191 <= a(9) <= 235**. Inherited numerical premises and the full graph-to-snake assembly remain unfinished. Contributor revision `852209db` reduces the estimated cost of its proposed 234 proof, but does not complete it.

The paper now develops forced-absence shares, exhaustive neighbour choices, count saturation, three direct count restrictions, arbitrary-length boundary accounting and complete-model history in logical order. The earlier zero-credit model is retained in an appendix. All 108 prior mathematical statements are preserved, with one historical referent clarified; eight new statements bring the total to 116. All thirteen printed snakes pass 118,673 pair checks, and all 164 labels and references resolve. The existing editor and repository sources are synchronized, with authors and hyperlink settings unchanged. The desktop editor compiler succeeded; rendered-page visual inspection was not performed.

Next research priority: Derive stronger empty-square share inequalities across the entire 70-state, 99-transition critical family, then test their effect in the complete model. Recovering the omitted ambiguous share pattern requires additional direction history or a proof valid for both compatible shapes. Manuscript revision 66 completes the ten-round cycle after revision 56. The next full paper rewrite is scheduled for milestone 76.


## Milestone 67: conditional 234 through empty-square charge, 29 October 2026

Current mathematical checkpoint: [milestone 67](milestones/67-critical-family-charge/README.md). Empty-square charging raises the complete recorded model's integer minimum to **2482/5** (normalized **1241/300**). Independent verification covers all **18,194,151 transitions**. Strengthening the omitted singleton contribution from 15 to 21 gives the conditional bound **m <= 2758947/11741 < 235**, hence **234 edges**. Twenty Lean modules and 250 theorem audits cover 63 geometric share inequalities, 25 cycle exclusions, two restricted potentials and boundary accounting. The full graph certificate, history interpretation and inherited numerical premises still require proof closure. The contributor-checked global interval remains **191 <= a(9) <= 235**. Contributor revision `97851813` contains further 234 preparation and a partial 233 probe; no new completed global bound is adopted.

The crucial boundary improvement pairs the first six omitted internal counts and uses positivity at the seventh. Together with both endpoints this gives 21, saving 720 in the window budget. The new complete-model potential has numerator 2482, denominator 5 and range 3238. Eliminating the total window weight yields 23482m <= 5517894; at m=235 the deficit is 376. This is a conditional deduction, not an arbitrary-snake upper bound.

Next research priority: close the proof obligations for the conditional 234 estimate, beginning with an explicit inventory of inherited numerical rules and the graph-to-snake history interpretation. The current mean and improved boundary accounting already suffice numerically. This is round 1 of 10 after manuscript revision 66; the next full paper rewrite is scheduled for milestone 76.


## Milestone 68: eliminate numerical share premises, 29 October 2026

Current mathematical checkpoint: [milestone 68](milestones/68-proof-dependency-pressure/README.md). All **24 numerical-only oriented share rules have been removed** while preserving the conditional bound **234**. The complete recorded model now has exact integer minimum **14392/29**, normalized **1799/435**, and potential range **18984**. Independent reconstruction checks all **18,194,151 transitions**; seven new Lean audits check the conditional arithmetic. The count catalogue still contains numerical exclusions: beyond the 1,287-key contributor reference, contiguous-subwindow reduction leaves 25,279 additional keys to assess. Complete graph-to-snake interpretation and Lean potential replay remain pending. The contributor-checked global interval remains **191 <= a(9) <= 235**. GitHub was refreshed; contributor revision remains `97851813`.

The cleaned weights invalidate 2,605 inequalities of the old potential. A new exact potential and attaining 29-edge cycle give 136192m <= 32003960, hence the conditional bound m <= 4000495/17024 < 235. The numerical share premise list is empty; remaining count premises are explicitly inventoried.

Next research priority: restore transitions excluded only by additional numerical count keys and identify which restorations violate a sufficient potential bound. This will target the count proofs needed for 234. All numerical-only share premises are now unnecessary. This is round 2 of 10 after manuscript revision 66; the next full paper rewrite is scheduled for milestone 76.


## Milestone 69: select exclusions for the conditional target, 30 October 2026

Current mathematical checkpoint: [milestone 69](milestones/69-count-certificate-selection/README.md). The conditional target **234** now requires **18,788 additional count keys**, using 1,378 reference keys from completed contributor proofs and no numerical-only share rules. The sufficient potential numerator is 14387 at denominator 29, with range 18984. Independent verification covers all **4,028,578 retained transitions** and every mandatory-key witness. Eight Lean audits cover the general selection argument and conditional arithmetic. Minimality holds only for the fixed potential and candidate basis. The selected count keys and complete graph-to-snake proof remain outstanding; the contributor-checked global interval remains **191 <= a(9) <= 235**.

The target numerator 14387 gives 136187m <= 32003920, excluding 235 by a margin of 25. A smaller integer numerator with the same denominator, potential range and boundary budget is insufficient. Reusing the earlier 236 catalogue adds 91 reference keys; relaxing the target removes 37 further six-count keys.

Next research priority: alternate conditional optimisation with proof-supported improvement of the unconditional route. The next round will build and test a model using only proof-supported count exclusions and share rules, then identify a useful missing theorem from the comparison. Conditional estimates and unconditional bounds must be reported separately. This is round 3 of 10 after manuscript revision 66; the next full paper rewrite is scheduled for milestone 76.


## Milestone 70: recover proved rules in the unconditional track, 30 October 2026

Current mathematical checkpoint: [milestone 70](milestones/70-proof-supported-share-model/README.md), on the proof-supported track. Forty previously checked short-window rules have been integrated, excluding **1,089,429 transitions**. Independent reconstruction verifies all **4,997,518 remaining transitions**, an exact integer mean of **480**, and potential range **578**. A four-transition cycle with exact counts 3,5,4,4 replaces the earlier 1,5,6 cycle. Five new Lean audits cover the recovered pair-theorem application and the bound arithmetic; 1,023 imported source hashes match their proof receipts. The contributor-checked global interval remains **191 <= a(9) <= 235**. The conditional target remains **234**, with the 18,788 additional count premises recorded in milestone 69. Complete graph-to-snake assembly and Lean graph-potential replay remain pending.

The old three-cycle is removed by a pair theorem already proved in milestone 49. Its integration avoids an unnecessary new SAT refutation. The exact replacement mean remains 480; even potential range zero cannot exclude 235 under the current boundary accounting. This establishes a limitation of the present comparison, not a new global theorem.

Next research priority: alternate to conditional optimisation using the forty recovered proved rules to reduce the remaining count-dependency selection, and evaluate stronger empty-square charge on the replacement critical configurations. The following proof round should certify useful new inequalities and advance arbitrary-snake assembly. Keep conditional targets and unconditional bounds separate. This is round 4 of 10 after manuscript revision 66; the next full paper rewrite is scheduled for milestone 76.


## Milestone 71: reduce conditional proof obligations, 30 October 2026

Current mathematical checkpoint: [milestone 71](milestones/71-proved-rule-conditional-pressure/README.md), on the conditional optimisation track. The forty recovered proved rules reduce the additional count premises for **234** from **18,788 to 14,155**, a reduction of **4,633 (24.66%)**. Independent verification checks all **3,533,981 retained transitions** and every mandatory-key witness. Recomputing the full conditional model raises its exact integer mean to **1492/3**, but the earlier potential needs fewer count proofs and is retained. Eight new Lean audits cover pruning and conditional arithmetic. The contributor-checked global interval remains **191 <= a(9) <= 235**. Selected count premises, complete graph-to-snake assembly and Lean graph-potential replay remain pending.

The same-potential selection is a subset of the previous one and is the unique least cover for the fixed graph, potential and candidate basis. The recomputed potential requires 16,077 keys, so its higher mean does not reduce proof cost. Both sufficient certificates imply 234; neither is a completed global proof. Even zero range at the new exact mean cannot support 233 under the current boundary budget.

Next research priority: return to the unconditional proof track and inspect the sixteen remaining four-count premises, reusing existing implications before generating new refutations. Evaluate their effect on the entire critical family. The conditional proof plan also retains 1,096 five-count and 13,043 six-count premises. Keep conditional targets and unconditional bounds separate. This is round 5 of 10 after manuscript revision 66; the next full paper rewrite is scheduled for milestone 76.


## Milestone 72: proof closure checkpoint, 31 October 2026

Active research: [milestone 72](milestones/72-four-count-proof-closure/README.md) is in progress. Ten certificate cases and thirty-two theorem audits are complete, including a returning-direction restriction with no middle-count assumptions. The checked additions remove 50,510 transitions and reduce the additional premises for conditional 234 to 14,143. The exact model mean remains 480 and the global upper bound remains 235. Six candidate certificate cases are still pending. The share-120 local theorem now passes 72 theorem audits across 99 modules; incorporating it reduces the fixed-potential count basis by one more premise, to 14,142, with the global assembly still pending. This checkpoint does not complete the research round.

The exact-count case (3,4,4,4) remains unresolved after two different bounded solver attempts. Completed source checks and graph receipts are preserved separately from pending certificates. The paper remains unchanged while the sixth round after revision 66 continues.


### Milestone 72 continuation: count-free share criterion, 2 November 2026

The [count-free investigation](milestones/72-four-count-proof-closure/critical-current/README.md) identifies four minimal shape covers of all 17,506 tight critical edges. Three share-12 premises raise the exact finite mean from 480 to 485, without changing the integer bound 235. The fixed-potential count list falls from 14,142 to 14,001 under these premises.

The stronger mixed target assigns share 20 to 012034, share 12 to 012310, and share 16 to the other seven canonical six-transition shapes. All nine Boolean refutations are independently checked and reconstructed from their encoders. An independent all-edge potential audit gives mean 496, range 600, and conditional bound 137941/587 < 235. Lean checks the conditional arithmetic with strict margin 32. The local share theorems, reversal normalization, global share representation bridge and complete snake-to-graph interpretation remain required. The unconditional interval remains 191 <= a(9) <= 235.

The initial forced-neighbour argument gives zero for all nine shapes. A relaxed zero-share example contains sixteen eight-cycles; valid cycle exclusions are essential for its case. All 24,366 windows in the 131 checked bank snakes have share at least 142, an observation on those examples only. Proof sources, exact comparison potentials, native certificates and reproduction scripts are retained under critical-current. The manuscript and editor mirror remain unchanged at revision 66.

The count-free distinct-direction share-12 theorem subsequently completed 221 Lean modules and 86 theorem audits. Both the uniform and mixed nine-shape targets have complete native certificates. The unconditional interval remains 191 <= a(9) <= 235; 234 remains conditional.


## Milestone 73: count-free catalogue and global accounting, 2 November 2026

Active research: [milestone 73](milestones/73-countfree-share-catalogue/README.md) checks three of the nine stronger count-free share cases: 012031, 012304 and 012314, each with share at least 16. The actual-snake shape coverage, canonical coordinate and reversal adapter, global share identity, and five-centre overlap are Lean-checked. The combined catalogue theorem now retains six explicit local certificate premises. The full target remains conditional 234; the contributor-checked interval remains **191 <= a(9) <= 235**. Complete graph interpretation and potential replay remain pending. Milestone 72 separately retains six unresolved count-certificate cases.

Count-free share continuation: [checked and conditional comparisons](milestones/73-countfree-share-catalogue/README.md) verify all 4,947,008 edges. Using only completed local shares gives exact mean 480 and potential range 536. Adding the single unproved share-12 premise for 012310 gives mean 483 and range 551; its integer comparison bound is 235. The full nine-shape catalogue has mean 496, range 600, and conditional bound 137941/587 < 235. An exact audit shows every selected share value is necessary for that fixed graph and potential. This does not prove optimality among other proof plans.

Next research priority: check case 7305, the count-free share-12 certificate for 012310, then complete the remaining catalogue and graph assembly. It complements the checked 012345 share-12 and 012314 share-16 rules in a minimal cover of the original critical family. Reproduction and remaining obligations are in [the continuation record](milestones/73-countfree-share-catalogue/NEXT.md). The manuscript remains at revision 66, with its next full rewrite scheduled for milestone 76.

## Milestone 74: graph interface, potential obstruction and handover, 2 November 2026

The current graph stores five count symbols per state and six per edge, with 1,601,856 states and 4,947,008 edges. Four new Lean identities check source, target and suffix direction normalization. A source audit pins contributor commit cd0c90fd and identifies the remaining history invariant, numeric coding, exact exclusion/credit coverage and full potential replay. The contributor's count-only seven-centre UpperBound234 composition used temporary stubs and does not establish a completed234 theorem.

Six exact graph relaxations have independently checked short walks of length7 through17 with deficit at least632 relative to496. They retain a three-edge cycle of mean496. A new Lean-checked algebraic lemma shows that no constant slope and global potential range on those entire relaxed graphs can satisfy the strict234 criterion under the existing boundary budget. This extends the earlier fixed-potential diagnosis, without proving optimality over different graphs, boundary estimates or geometric constraints.

Case7305 now has92 successful semantic/composition modules. Dependency slicing reduces its refutation from224,393 to154,489 derived clauses and from12,625,945 to9,394,822 hints. Independent simulations passed;15-bit encoding is still required and no replay speed improvement was measured. All465 sources, selected compact proof and original proof evidence are archived and hash-verified. Lean refutation replay and the final geometry/reversal audit remain pending. The completed stronger catalogue remains7300,7304,7306, with six target cases unresolved.

The [2 November handover](handoff/2026-11-02/START_HERE.md) preserves mathematical conclusions, evidence levels, reproduction limits, precise next tasks and a reusable prompt for other agents. The interval remains191 through235, and234 remains conditional. The paper and existing editor source remain unchanged and hash-matched at revision66.

## Milestone 75: exact history, lookup and count-code components, 2 November 2026

After the requested pause and subsequent resumption, the selected case7305 LRAT replay was started from unchanged archived sources. Its checker and large proof checkpoints are passing. A frozen snapshot records only completed source/object/log-matched modules, while the live driver may continue; the final share theorem remains pending.

Thirty-nine new Lean audits check three required graph-interpretation components. The longest-dictionary-suffix invariant identifies emitted three-ID signatures and excludes emission in the first two steps; its exact75-entry dictionary and58 signatures are checked. A complete six-direction check proves the graph's lexicographic orientation agrees with the conditional share dispatcher and uses centres r+4 through r+8. Numeric proofs establish base-six prefix/suffix extraction, entering-count recovery, the exact1,601,856-state index range, and saturation-safe guards. These do not yet establish complete actual-snake graph membership or the global potential theorem.

Contributor commit1e0ebb95 adds handover documentation and still records unfinished234 production work. The accepted project interval remains191 through235. A read-only proof-planning test found795 unused initial clauses; their immediate reuse would still require15-bit encoding, so the active export was preserved. The next manuscript rewrite remains milestone76. Current continuation instructions are in [handoff/README.md](handoff/README.md).

## Milestone 76: paper revision and conditional arithmetic, 2 November 2026

Current manuscript revision: [milestone 76](milestones/76-paper-revision/README.md). The revised argument includes boundary contribution 21, completed and pending shares, exact history recognition, conditional 234 and the short-walk obstruction. All 116 old statements and 13 snakes are preserved; seven additions give 123 statements. All 180 labels and 118,673 vertex-pair checks pass, as do six new Lean arithmetic checks. The editor and repository sources match, with authors and hyperlink settings preserved. The app compiler failed before source compilation; no updated PDF is verified.

The built-in compiler diagnostic and a frozen snapshot of successful case 7305 replay modules are saved. The final local theorem remains pending. The current interval is 191 through 235; 234 remains conditional. The written converse-emission argument is distinguished from the checked history invariant and soundness results.


## Milestone77: direction and history-shape interfaces

2 November 2026. 106 printed theorem audits passed Lean4.19.0. Every actual eight/nine-direction window has a valid recorded ID, with consecutive source/target states; numeric history decoding, signature equivalence and nonempty-history shape compatibility are checked. Finite coverage and lookup are split into kernel-checked blocks to control memory. The concrete history update, combined count state, exclusions, credits, retained edges and full potential interpretation remain. No numerical bound changed. Case7305 final share theorem remains pending; successful replay rows and actual process observation are frozen in milestone77. Paper revision76 is unchanged and hash-matched; the compiler retry failed before source compilation. The current handover and continuation prompt are in handoff/.


## Milestone 78: numeric history transitions and actual state sequence

2 November 2026. Four modules passed 29 Lean theorem audits. The strict maximum-suffix scan agrees with actual history updates; ties and empty fallback are covered. A rechecked count identity supplies positivity for the actual core counts. The combined direction, history and five-count states have correct numeric endpoints and both history compatibility filters. An executable comparison of the exact builder selector covers all 37,875 pairs. The retained-edge and charge interpretation remains, as do six local share targets and complete potential replay. No numerical bound changes; the case7305 refutation continues under its existing driver. Paper revision76 remains unchanged. Evidence and the precise next task are saved in milestone78 and handoff/.


## Milestone 79: encoded guards and ten interval exclusions

2 November 2026. Six modules passed 31 Lean theorem audits. Base-six slices and digits agree with actual singleton counts; encoding injectivity, coordinate normalization, reversal and interval saturation are checked. The ten completed milestone72 interval refutations now imply retention under their encoded graph filters, at all three offsets and in both orientations. Existing certificate objects were reused with source/object hashes, without a clean rebuild of their entire dependency closure. The 1378-key reference union has inspected contributor proofs but is not instantiated in this environment. Recovered short rules, history exclusions, array membership, credits and potential remain. The finite audit covered 2799360 interval-guard comparisons. No numerical bound changed. Case7305 remains pending until its final local audit passes; the exact observed process and successful modules are saved in the checkpoint. Paper revision76 is unchanged.


## Milestone 80: the 012310 share theorem

2 November 2026. The selected case7305 refutation completed Lean replay, followed by geometry, reversal and the full source/axiom audit: 465 modules and 100 audits. Every matching six-transition snake window has five-centre scale12 share at least 12, without an extra singleton-count hypothesis. Archives restore all 465 sources and compact proof bytes. The combined catalogue passes 35 audits and retains only cases7301, 7302, 7303, 7307, 7308. The exact finite comparison verifies all 4947008 edge inequalities and an attaining cycle: mean 483, potential range 551, bound 157625/669 and integer 235. Its weights and potential match the formerly assumed012310 comparison. No new global numerical bound follows until the graph/credit/potential assembly is complete. All case7305 proof processes have finished. Paper revision 76 is unchanged; the next scheduled rewrite is86.


## Milestone 81: retention under forty recovered short rules

2 November 2026. Eight Lean modules passed 66 printed theorem audits. All forty recovered short filters now preserve actual snake windows at every fitting offset and in both orientations, with explicit represented-position and count-saturation conditions. Three small semantic support sources were checked again; 970 certificate objects were reused with pinned source/object hashes. The exact builder-loop comparison covers 23,561,280 direction/count pairs and 7,927 placements, with reconstructed and hash-pinned inputs. Independent review found no outstanding defect within this scope. The reference union, three history exclusions, retained-array membership, credits and potential replay remain. The maintained interval stays 191 through 235; 234 retains five local share targets and global assembly obligations. Paper revision 76 is unchanged, with the next full revision scheduled for 86. All receipts, exact manifests and continuation instructions are saved locally.


## Milestone 82: unsaturated-cycle obstruction

2 November 2026. The completed-share graph retains a four-edge cycle of mean 483 whose six-count symbols are all below six. Every nonnegative bonus vanishing on this class preserves the exact mean; the old potential remains valid and the same cycle attains it. Six Lean audits check count literals, cycle telescoping, monotonicity and the strict-budget obstruction. All 4,947,008 edge inequalities and the exact cycle were independently rechecked against saved array hashes. At range zero the 234 criterion already lacks 2319 charge units. Cases 7302 and 7307 would raise this one witness to 497 if their target share bounds are proved; this is not a new whole-graph mean. The interval remains 191 through 235, all five target local shares and global assembly obligations remain, and paper revision 76 is unchanged.


## Milestone 83: 012034 share-20 preparation and conditional pressure

2 November 2026. Case 7302 is being promoted from the saved native refutation to a Lean local theorem. The target is 20 on shape 012034 with all five counts in [0,21] and no cycle cuts. Independent review checks all 99,818 native clauses, 15,446 selected core clauses, compact renaming and generated Lean literals. All 121 semantic shards and their assembly passed, for 127 modules. Compact LRAT generation, original export simulation and reduced export simulations passed; final Lean replay is recorded separately in the live checkpoint. The local theorem remains pending until geometry, reversal and the complete source/axiom audit pass.

The exact finite comparison adding only the unproved 012034 floor 20 raises 1,043,097 edges over the completed-share model. Its mean is 9259/19, scaled range 11301, and bound 20965613/89059, giving 235. A separate verifier checks every edge and an attaining 19-cycle; three Lean audits check conditional arithmetic. This target alone cannot reach 234 under the current budget, even at range zero. The global interval and completed local catalogue are unchanged. Paper revision 76 remains current; next full revision 86.


## Milestone 84: complete three-history exclusion transport

2 November 2026. Eight modules passed 38 Lean audits. Three emitted history IDs identify the actual overlapping nine-direction windows; each exclusion signature has exactly one compatible induced eleven-direction word. The existing count lower bounds three then contradict digit caps two at the correct positions. The final theorem applies to every actual snake and fitting step without an unresolved local certificate premise. The small helper and count proofs were replayed in the current window environment after an older import closure caused duplicate declarations. Definitions and proof bodies were retained.

Independent complete enumeration covers all 11,162 canonical induced eleven-words. The actual isolated builder loop agrees on 37,875 history/direction pairs with six uniform count vectors each, followed by all 46,656 count codes for each of the three active pairs. These are filter tests, not full-graph edge counts. The reference union, retained-array index, credit interpretation, potential replay and five local share targets remain. Case 7302 continues under the existing driver. The interval remains 191 through 235; paper revision 76 is unchanged and the next full revision is 86.

## Milestone 85: exact reference catalogue union

2 November 2026. The pinned 235 and 236 catalogues contain 1,287 and 732 keys, with intersection 641 and union 1,378. Every canonical representative occurs directly in a source list; the selection uses the 1,287 first-catalogue entries and 91 additional second-catalogue entries. Twenty-seven modules passed Lean with 103 printed theorem audits. The exact finite table, source membership, valid widths and symbols, and forward/reverse retention for every fitting actual-snake window are checked. The final retention theorem retains AllRefuted6K235 and AllRefuted236 as explicit premises. The bounded provenance audit found the historical source theorems and successful Linux logs, while matching locally importable closed proof objects remain absent.

The isolated reference-filter comparison covers all 505 direction extensions and 46,656 count codes, giving 23,561,280 pairs. It accepts 3,899,352 and rejects 19,661,928; these are not newly removed full-graph edges. Direct digit folding independently checks the builder's quotient/remainder slices. The direction conventions are shared between implementations and were checked against the Lean window lemmas in source review. The exact retained-array index, closed catalogue imports, credit interpretation, complete potential replay and five local share targets remain. Case7302 continues under its existing driver, with a frozen observation in this checkpoint. No global bound changes; paper revision76 remains current, with full revision 86 next.


## Milestone 86: paper revision and proof scope

2 November 2026. The existing editor document and repository mirror now incorporate milestones77–85. The paper has 130 statement blocks:122 previous statements unchanged, the count-independent share theorem strengthened by012310>=12, and six new propositions and one definition for the actual state sequence, filters, history exclusions, conditional reference union and unsaturated-cycle obstruction. All original appendix content,13 printed snakes and118,673 vertex pairs are preserved and checked. All190 labels resolve; authors and hyperlink metadata are unchanged. Seven fresh Lean checks cover the abstract cycle-family argument and conditional comparison arithmetic.

The completed-local model is now clearly identified as mean483, range551; mean480 is historical. The pending012034 floor gives9259/19 with scaled range11301 and still integer235. The full496/600 comparison remains conditional234 with five local shares, closed reference imports, retained-array membership, credit interpretation and complete potential replay pending. The built-in compiler again failed before reading the TeX source because of its Windows execution environment; no updated PDF is verified. The complete original was independently read, all additions reviewed, and history-notation and converse-status issues corrected. Case7302 continues under its existing driver. The next scheduled paper revision is96; the next proof task is exact retained-array membership under the current explicit premises.

The user's subsequent request encouraged explicit definitions. The revision adds the zero-bonus subgraph and the exact critical-cycle criterion: for a fixed finite graph and nonnegative edge bonuses, the minimum mean increases precisely when every old critical cycle receives positive total bonus. Seven additional Lean checks establish finite attainment, monotonicity, equality/strictness equivalences and the required nonnegative-sum facts, bringing the total to14. This criterion explains the saturation obstruction and does not itself establish234 or the validity of new local shares.


## Milestone 87: retention covers and saved-edge indexing

2 November 2026. 27 fresh Lean theorem audits combine all retention families,
prove an executable bounded predicate true for each actual snake step and
assemble a complete saved state walk under explicit finite coverage and
endpoint-column premises. The two reference-catalogue premises remain.
The retention-cover definition isolates the weaker inclusion sufficient for
membership; exact generator equality and duplicate-free key indexing have
generic checked interfaces. No proof identifies an edge only by its endpoints.

Independent executable reconstruction agrees on 36,904,896 compatible candidate
keys, 791 compatible blocks and every one of the 4,947,008 saved rows. All
37,084 incompatible blocks are empty. Ordered full keys are unique, but
206,589 endpoint pairs have multiplicity two. Every stored endpoint agrees
with the source formula. The arrays remain computationally audited rather
than supplied as a closed Lean finite coverage certificate. Weight validity
and full potential replay are still separate. Source/object hashes for the
combined inherited support are checked; that closure is reused, not rebuilt.

The 791 blocks share 127 distinct count-code sets. A 3,981-node membership
diagram reproduces every set; a second integer-digit decoder agrees on
5,925,312 inputs. The complete compressed data is 29,924 bytes. Its Lean
coverage implication remains the next finite proof obligation.

The paper remains revision 86, with the next scheduled full revision at 96.
The maintained interval is 191 through 235; 234 remains conditional. Case7302
continues through its existing driver without duplicate replay. The new
checkpoint preserves its current successful rows, logs and process observation.


## Milestone 88: rejection boxes and a checked coverage pilot

2 November 2026. The round adds 26 Lean theorem audits: box-prefix containment,
digit reconstruction, four rejection-witness families, six-way coverage,
numeric-retention assembly and three concrete pilot checks. Two additional
data modules compile with no theorem audits. Every printed theorem uses only
standard axioms; the pilot coverage equation uses none. Inherited objects
are reused without a complete dependency rebuild.

For direction 0 and history 0, all 375 witnesses and the coverage tree pass
kernel checks. The retained-code membership theorem follows. There are 723
distinct tree nodes, 11,869 expanded visits and 6,123 accepted codes. The
concrete proof module takes 92.594 seconds; graph and pilot data compilation
take 96.219 and 46.203 seconds respectively.

Computational box reconstruction agrees on all 791 compatible blocks and
4,947,008 rows. Maximum-uncovered selection retains 356,548 direct occurrences,
1,369 fewer than the preserved baseline. Every selected direct box has a
private code; no minimum-size cover is claimed. The more useful reduction
finds a common geometric cover in all 127 membership classes, with 82,659
class-box occurrences. Context-specific witness lists for those common
covers still need materialization and Lean checks.

All-context finite coverage, diagram-to-row identification, endpoint columns,
the two reference-catalogue premises, credit interpretation and full potential
replay remain open. The bounds remain 191 through 235, with 234 conditional.
The paper stays at revision 86, next scheduled revision 96. The existing
case7302 replay continues; its partial logs are preserved in a delta snapshot
with reused and freshly hashed objects distinguished.


## Milestone 89: shared-cover checkpoint and balanced lookup

2 November 2026. This checkpoint records 28 Lean audits: four history-transport,
four separate-list assembly, two array-checker equality, five balanced lookup,
two general lookup-checker equality, three concrete graph-table and eight
concrete class 0/class 1 results. The full 127-class run remains active. All 127
trees are generated and pointwise replayed over 5,925,312 class/code pairs.

All 543,827 context-witness occurrences are materialized with original rule
indices, covering 791 contexts. Deduplication gives 211 aligned lists and 4,387
constructors. Only three occurrences use history, always at position zero.
The remaining witness equations, context assignment and graph interpretation
remain explicit. The source/data reviews preserve their own earlier snapshots.

Two lookup experiments were stopped without a cover proof after 685.187 and
475.312 seconds. Balanced class 1 succeeds in 51.828 seconds; class 0 in 66.453 seconds.
The experiment was concurrent, so no controlled speed ratio is claimed. The
graph compiler succeeded; an overly strict zero-axiom audit expectation was
corrected while preserving its successful output and original checker bytes.

Case7302 timed out at Check66, then a resume encountered a stale temporary
output error. The unique-output resume passes Check66 in 130.02 seconds and
continues through unchanged proof sources. Failed attempts are preserved.
Distinct successful modules are counted separately from repeated composition
rows. Bounds remain 191 through 235, with 234 conditional. The paper stays at
revision 86, next full revision 96. This checkpoint does not mark the full
geometric batch, the local share theorem or the overall goal complete.


## Milestone 90: witness compatibility and count conditions

2 November 2026. 17 Lean audits check generic lookup substitutions, exact
balanced direction/reference tables, six class-1 witness assignments and
their numeric-retention implication, and general witness factorization.
The concrete pilot covers 3,840 validity entries across six directions and
extends to every bounded history under the original predicate. Its proof
module took 21.125 seconds. Full context assignment remains open.

The all-context plan contains 507 base validity jobs and three separate
history heads. Its 357,823 entries share 15,353 normalized shape tests and
2,651 count tests, with 508 outer and 2,329 catalogue guards. Every saved
entry comparison agrees. Reference keys account for 338,697 entries and
only 12,560 normalized shape tests. This is computational evidence for a
same-class sharing experiment; concrete descriptor equality and assembly
are still required, and no timing improvement is claimed.

The checkpoint observes classes 0 through 12 completed in the continuing
127-class geometry run and 449 distinct successful modules in
case7302. Exact logs, dependency pins and live-state snapshots are saved.
Neither process is restarted. Bounds remain 191 through 235, with 234
conditional. Paper revision 86 is unchanged; the next rewrite is due at 96.


## Milestone 91: certified reference-pattern reuse

2 November 2026. Eight new Lean audits check generic bounded shape substitution
and the same six-case membership result using 156 cached patterns for 3,732
reference occurrences. Catalogue, placement and index guards, complete descriptor
equality and zip lengths are checked. The 108 nonreference occurrences retain
their original compatibility tests. The direct source is byte-identical to 90;
its two theorem audits are repeated for timing and add no new results.

Direct trials took 18.812/37.875 seconds; cached trials 24.203/28.016 seconds,
including descriptor and assembly checks. Generic/data setup adds 46.125/45.219
seconds. Concurrent load was not controlled. No speed advantage is established,
so the next full batch will use the direct balanced-lookup checker and the
saved 507-job/three-head plan. Exact trial logs and hashes are preserved.

The checkpoint observes geometric classes 0 through 19 and 493 distinct successful
case7302 modules. Both jobs continue. Bounds remain 191 through 235, with 234
conditional; paper revision 86 is unchanged. The full research goal remains open.


## Milestone 92: context assignment and full witness batch

2 November 2026. Milestone 92 checks the complete source-compatible context assignment over
37,875 direction/history pairs, including the three history-dependent class
overrides and exact agreement with the saved block classes and roots. This
check enumerates no count codes. The frozen checkpoint has 65
Lean theorem audits, 3 of 127 concrete witness classes, 43 geometric classes
and 649 distinct successful case7302 modules. These are snapshot counts.

The all-class witness process is active in tool session 97444, alongside
geometry session 23168 and replay session 14427. Inspect actual process state
before any resume; do not duplicate live jobs. All 507 base jobs and three
leading history witnesses are generated and independently reviewed. The final
family assembly requires every class receipt and is queued after the batch.
The exact checkpoint states whether that final theorem has passed.

The chosen next proof object is the graph defined directly from diagram-accepted
full keys, with endpoints computed from each key. This avoids a separate identity
with external row and endpoint arrays if all weight and potential certificates
are checked on the defined graph. Keep the two reference-catalogue premises,
pending local shares, credit interpretation and complete potential explicit.
The interval remains 191 through 235 edges, with 234 conditional. The contributor
upper-bound proof still needs a complete independent rebuild. Paper revision 86
and its three authors and hyperlink settings are unchanged; the next full
revision is scheduled for milestone 96.


## Milestone 93: joint slope and range comparison

3 November 2026, Japan time. Latest continuation: [milestone 93 checkpoint](milestones/93-defined-graph-potential/README.md) adds seven Lean comparison audits. Independently checked cycle and path certificates prove joint optimality of the slope and global potential range on each of the three fixed weighted array graphs. Their integer comparisons remain 235, 235 and conditionally 234. The snapshot records 7/127 witness classes, 55/127 geometric classes and 649 successful case7302 modules. The witness and geometry batches continue; case7302 stopped after a 900-second Check1 timeout. Bounds remain 191 through 235, with 234 conditional; paper revision 86 is unchanged.

Next research priority: prove the exact key-dependent five-centre credit bound, especially complete coverage of compatible eleven-transition words for all 55 history share rules. Continue the existing witness and geometry batches. The recorded fixed-model comparisons cannot be improved by changing only the constant slope and global potential range. The defined graph still needs its complete weight and potential checks. For case7302, test one isolated replay segment before changing or restarting the timed-out six-segment check. Keep the two reference-catalogue premises and all five pending local shares explicit.

The new comparison is checked in Lean under explicit graph-witness hypotheses. Concrete embedding and every array potential inequality were checked numerically by two implementations. This does not discharge the actual-snake credit theorem or the complete potential check on possible extra diagram rows. All original paper bytes are preserved. The exact optimum remains unresolved.


## Milestone 94: complete history-share configurations

3 November 2026, Japan time. Latest continuation: [milestone 94 checkpoint](milestones/94-history-share-dispatch/README.md) checks all 55 history-share signatures with 73 Lean theorem audits. Their exact compatible sets contain 69 words: 41 signatures are unique and 14 have two variants. Actual-window recognition and generic count-cap transport are checked. Every needed local credit has an identified historical theorem; concrete instantiation in a compatible import environment and maximum-credit dispatch remain. The frozen snapshot records 31/127 witness classes and 64/127 geometry classes. Bounds remain 191 through 235, with 234 conditional; paper revision 86 is unchanged.

Next research priority: connect the existing per-word share theorems to the current share definition. Start with the credit-2 rule FamilyCharge67.G000, using a uniquely named compatible support module and the checked history classification; then extend to all 69 geometric and eight capped bounds. Old ShareFrame and current LocalWindowShareBridge declare identical coreShare text under different module ownership, and five instance-module names collide. Resolve these imports and recheck the selected source closure before combining applicable credits by maximum. Continue the witness and geometry batches. Preserve case7302's stopped Check1 replay until a controlled isolated test.

Two complete numerical enumerations agree with the generated lists. Lean checks both coverage and validity of all listed words. The source audit identifies 77 historical local theorems across 29 modules, with 42 reused geometry results checked separately. The compatible local-credit port remains to be compiled; no new local share bound or global numerical bound is claimed.


## Milestone 95: concrete history-credit integration

3 November 2026, Japan time. Latest continuation: [milestone 95 checkpoint](milestones/95-history-credit-integration/README.md) supplies all 69 geometric and eight capped word bounds for the 55 history-share rules. Their maximum is Lean-checked against the actual five-centre share sum, in the same environment as the defined graph. The source closure and adapters passed 923 theorem audits. The frozen snapshot records 86/127 witness classes and 89/127 geometry classes. Bounds remain 191 through 235, with 234 conditional; paper revision 86 is unchanged.

Next research priority: revise the existing paper at milestone 96, using standard notation and defining only essential recurring concepts. Then combine the remaining graph-weight components with the checked history credit and verify the complete potential on the defined graph, including conservative extra rows. Continue the witness and geometry batches. Preserve case7302's stopped Check1 replay until a controlled isolated test.


## Milestone 96: paper revision

3 November 2026, Japan time. Latest continuation: [milestone 96](milestones/96-paper-revision/README.md) integrates the completed history-share bounds, conditional accepted-key graph coverage and joint slope/range comparison into the existing paper. It adds four statements and a complete 55-rule table, with zero new named definitions. The frozen checkpoint records 99/127 witness classes and 99/127 geometry classes. The interval remains 191 through 235, with 234 conditional.

Current manuscript revision: [milestone 96](milestones/96-paper-revision/README.md). All 130 prior statements and the original appendix body are preserved; four statements bring the total to 134. All 13 printed snakes pass 118,673 vertex-pair checks, and all 199 labels resolve. The 55-row history table matches the checked 69-word catalogue and eight capped bounds. Authors and hyperlink settings are unchanged, and the editor and repository sources are identical. The built-in compiler could not start its helper, so no updated PDF or layout check is claimed.

Next research priority: combine the remaining graph-weight components with the checked history credit, retaining the actual full edge key, and verify the complete potential on the defined graph, including conservative extra rows. Continue the existing witness and geometry batches. Keep the five unfinished target floors and two reference-catalogue premises explicit. Preserve case7302's stopped Check1 replay until a controlled isolated test. The next scheduled full paper revision is milestone 106.


## Milestone 97: geometric integration and least pending floors

3 November 2026, Japan time. Latest continuation: [milestone 97](milestones/97-geometric-credit-integration/README.md) integrates all 505 geometric credits and their maximum with the 55-rule history credit for actual snake windows. The finite-graph sensitivity certificates show that the least pending floor vector in the original integer target box is (16,18,16,16,16): the 012034 requirement drops from 20 to 18. The revised potential has slope 496, range 602 and strict margin 30 for conditional 234. All 127 numeric coverage classes and their final graph-walk assembly are checked under the two reference-catalogue premises. The global interval remains 191 through 235.

Next research priority: instantiate the four count-conditioned rules and share-120 in the checked symbol-transfer interface; assemble the completed and conditional count-free profiles, using the weaker 012034 target 18. Then check the potential on the same defined graph. Preserve the original case7302 target-20 replay; any new target-18 refutation must use separate files. Keep the two reference-catalogue premises explicit. Paper revision 96 is unchanged; the next scheduled full revision is 106.
