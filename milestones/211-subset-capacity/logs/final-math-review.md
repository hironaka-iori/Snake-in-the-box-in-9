# Final mathematical review of round 211

Reviewed the complete new subsection sec:subset211, paper/snake9_research.tex lines 6692–6785, with its preceding square-capacity argument; the new short-explanation paragraphs at lines 323–368; Sharing211.lean; all three ConcreteSpare sources; and the six saved audit receipts plus completion.json. No paper edits, compiler, tests, solver, or native search were performed.

Document hashes at review:

- paper/snake9_research.tex: ef91f3ee2041e675a10e5928115dc2fce2f939eff5d3d370d9d31706de22d841.
- paper/snake9_frontier_explanation.tex: c9fd6a6b49f4034950f3c8cdcd549ed13a67be29aa899335b495b3c7566b08ea.

No incorrect deduction or missing mathematical premise requiring a correction was found in the reviewed passages.

## Assumptions and scope

- Lines 6700–6722 correctly require distinct assigned words, finite domain containment, and an additional conflict with every subset member before pruning an external interval. The nine singleton intervals are correctly excluded from automatic whole-family removal.
- Lines 6759–6769 concern the saturated 32-variable family over its 32 parity words. A covering matching therefore uses every alphabet word. This is the reason every domain word has an owner and a reachability closure is tight. The argument is not transferred to the unsaturated families; their unmatched words would require separate treatment.
- Lines 6725–6757 correctly count outside intervals through their assigned words: within the fixed parity, equal words at equal corners repeat a vertex, while equal words at distinct outside corners create a chord because the two corners are adjacent. The chosen and outside families each have distinct assigned words, although the two families may share words.
- The three table rows agree with the literal-count declarations: (4,7) even gives clique/outside sizes 31/2, (0,6) even gives 30/9, and (0,6) odd gives 26/13. Their forced-sharing minima are respectively 1, 7 and 7. The text correctly leaves the identities of the sharing intervals undetermined.
- Sharing211.forced_sharing proves the list version of the displayed shared-word inequality. Its private split_count partitions the outside list into words present and absent in the clique list. Nodup makes the filtered-list length equal to the number of shared words, and hence to the number of sharing outside intervals.
- The concrete partition results establish source-derived interval-index counts and coverage. They do not independently establish distinct assigned words in arbitrary targets. Lines 6753–6757 and short-explanation lines 363–366 correctly reserve the complete geometric assembly as a written argument with Lean assembly pending.

## Saved verification and search status

The six audit receipts report PASS and compiler exit 0, with 4, 3, 4, 3, 3 and 2 theorem reports, respectively: 19 total. Their reported axiom lists contain only propext and Quot.sound, with the two source_intervals reports using propext alone. This is a reading of saved evidence, not a fresh compiler replay or a complete independent dependency audit.

The completion record agrees with the prose: 196 new continuation steps, 296 cumulative steps, 11 pending regions, and 3,721,372 cumulative nodes. The reviewed text preserves native status for matching discovery, concrete pruning and traversal; it claims neither a completed new six-coordinate exclusion nor a speed improvement or global bound. The unsaturated-family constraints are correctly described as unimplemented next work.
