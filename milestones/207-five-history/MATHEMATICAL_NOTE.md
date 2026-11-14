# Round 207: five-coordinate rigidity and whole-path symmetry

The working hypothesis was that quotienting the remaining coordinate permutations could make the five-coordinate searches tractable and might reveal a different 98-edge Q8 parent. The complete native census resolves all 56 models, and none yields a different class. The constructive part of the hypothesis therefore fails for this fixed source and indexed comparison.

## Symmetry reduction on the whole snake

Round 206's exact model fixes the base words at every path index and gives each maximal interval of consecutive base edges one arbitrary block-word variable. A candidate is a complete induced path exactly when every consecutive pair has total Hamming distance one and every other pair has distance at least two. Its normalized initial block word is zero and its first block transition uses coordinate zero.

For five block coordinates, the remaining permutations of coordinates 1 through 4 form a group of 24 maps. Apply a permutation to every interval word, hence to every selected vertex of the whole snake. Hamming distances, parity, indexed base histories and both normalizations are preserved. Each finite orbit has a lexicographically least interval tuple. Retaining these least tuples preserves every orbit. Stabilizers are allowed; division by24 is unnecessary.

The excluded source-isometry assignments are also closed under these permutations. The generator fixes the input columns used by the base coordinates and enumerates every bijection of the remaining input coordinates to the block outputs. Composing any such assignment with a residual block permutation gives another enumerated assignment. Thus orbit coverage applies to the normalized model after those complete tuples are excluded. Independently, every genuinely different ambient cube class has an orbit avoiding every excluded tuple, because every exclusion is explicitly source-isometric.

For a fixed permutation \(\pi\), scan the chronological domains. If all values in every earlier domain are fixed by \(\pi\), an admissible current value must satisfy \(u\le\pi(u)\). A larger value would be the first lexicographic difference and would violate the representative condition. Remove those larger values. Continue only if all retained current values are fixed. If even one retained value satisfies \(u<\pi(u)\), the scan must stop: that choice already makes the inequality strict and permits any later comparison sign. Mixed fixed/smaller domains also require stopping.

This deletion preserves every lex-admissible completion of the current domains. It can be interleaved with sound binary propagation and complete branching, even when individual branches are not invariant under the group. The global orbit representative has a branch, and no sound deletion removes it.

Lean accepts the finite-minimum, closed-family representative and fixed-prefix deletion arguments, with seven dependency reports. Concrete action/model integration and the native finite search still have separate proof obligations. The source review covers those mathematical connections in writing; no Lean search certificate is claimed.

## Complete five-coordinate result

All \(\binom85=56\) choices exhaust. Every successful model object matches the corresponding round206 object exactly. The first batches resolve 52 cases; longer runs resolve the remaining indices 6, 12, 37, 43. Those final runs take 236727, 185130, 384434 and 308908 search nodes, respectively. The selected successful records total 1,526,383 nodes and 61.125 seconds of solver time. Earlier limited/interrupted attempts and preparation time are excluded from that total. The implementation language and symmetry reduction both changed, so these timings do not isolate the effect of symmetry alone.

Each model excludes 24 explicitly witnessed source-isometric normalized assignments. Exhaustion of the lex-restricted search covers every remaining orbit, by the preceding argument. Undoing normalization preserves ambient cube-isometry class. Therefore, at the native-enumeration evidence level, every induced 98-edge target retaining any three indexed coordinate histories of this saved parent is cube-isometric to it. A different class requires at least SIX changed histories at the same length and index matching. Changes to fewer free coordinates are subfamilies of these models.

This is not a classification of all optimal Q8 snakes. It does not show that six changed histories suffice, and it supplies no global Q9 length bound. The complete finite certificate in Lean is pending, including normalization, concrete table interpretation, branch coverage and isometry exclusions.

The native solver and Python orchestration were independently reviewed. The C implementation uses exact finite masks, transposed binary relations, whole-domain support deletion, complete forbidden tuples, the fixed-prefix lex rule, and exhaustive branching over the selected domain. Limits propagate separately from exhaustion. No software tests were created or run.

Some runs stopped at the unchanged memory thresholds. Session 13632 ended with exit 1 before case 50; its 37 completed case records were recovered from saved per-case files and progress, without rerunning them. The recovered report explicitly distinguishes its reconstructed provenance from a normal final report. Source, executable, model and input identities are retained. All 56 final selected exclusions have terminal per-case records.

## A short obstruction to reversal

Every cube isometry has the form \(f(x)=\pi(x)\oplus b\). Hence

\[
f(x)\oplus f(y)=\pi(x\oplus y).
\]

Equal coordinate-difference words must remain equal. In the saved parent, the edges at zero-based positions 1 and 4 are \((1,3)\) and \((15,13)\). Both have difference 2. A reversal would send them to \((70,68)\) and \((85,21)\), whose differences are 2 and 64. This is impossible.

Lean checks the general cancellation and parallel-difference preservation, the concrete word identities, the eight index identities in the literal 99-vertex source, and the impossibility of reversing that entire source. The module has ten dependency reports. It does not need a separate assumption that the coordinate map is bijective: the obstruction already excludes every coordinate-affine map of the displayed form.

This concerns an ambient map reversing the saved ordered snake. Transformations that change the whole embedding remain a different question. No full setwise-stabilizer classification or new kind of symmetry is claimed here.

## Current frontier

The next construction family frees six coordinates, leaving two histories fixed. All 28 cases reach the two-second limit in the selected terminal screen records. Earlier memory-interrupted attempts are retained separately. No six-coordinate exclusion or new witness is obtained; all 28 cases remain unresolved.

The most useful next optimization is durable branch continuation: retain unfinished domains at a time or memory stop so subsequent work extends the search instead of repeating its completed portion. This requires an exact coverage argument for the saved frontier, together with the existing global lex constraints. No continuation implementation or proof is claimed in this round. Restricting attention to one finite family still cannot prove the Q9 optimum.

The numerical Q9 frontier is unchanged: a 191-edge construction is retained; the archived 235 argument awaits its full independent rebuild, and the 233/234 comparisons remain conditional. The prediction 196 remains unresolved. The refreshed contributor branch reports 3,120 of 3,127 modules at 09:55 UTC on 14 November 2026; this is contributor-reported, unmerged progress.

The goal remains active. The user explicitly instructed continued work until she requests a stop. No new pause is scheduled.
