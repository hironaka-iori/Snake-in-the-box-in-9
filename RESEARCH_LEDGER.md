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
