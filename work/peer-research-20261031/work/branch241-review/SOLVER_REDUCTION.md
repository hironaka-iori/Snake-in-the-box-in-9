# Search-only deactivation prototype

solver_reduced.Solver takes STATIC clause axioms and an explicit RUP proof prefix. It verifies that prefix itself before constructing the search database, and sets reducible_from=len(static). There is no API accepting an arbitrary integer boundary for an unproved initial clause list. This prevents a caller from silently designating unverified input axioms as disposable learned clauses.

At a conflict-analysis boundary, candidate clauses must have IDs at or above that static boundary, currently occur in a watch list, contain more than two literals and not be already inactive. Every current reason clause is protected, using reasons of all assigned variables, including root assignments. The current conflict is separately protected. Ranking selects longer and older eligible clauses, then removes only their watch entries. Binary implication lists are unchanged because binary clauses are never candidates.

The original clause array, every clause ID and all emitted proof steps remain intact. Existing RUP hints can continue to name clauses that are inactive for search. The solver's final SAT model is still checked against every original clause record, not only active watches. Restoring from a checkpoint reconstructs all logical state as usual; this prototype does not persist a partially processed trail.

The constructor prefix is entailed by the static CNF, and every newly learned clause must pass the independent RUP checker before a research result is accepted. Consequently deactivating a learned clause weakens search propagation without removing a static premise or invalidating the permanent proof database. This does not constitute memory reclamation of the clause bodies or proof records: only watch activity is reduced.

## Tests

400 independent random mixed2/3-CNF instances were compared with exhaustive enumeration under two feature configurations. Every SAT model was checked against the original formula and every learned proof clause replayed. More aggressive PHP tests exercised actual deactivation:6 clauses on PHP5-into-4 and112 on PHP6-into-5, with independently checked final UNSAT proofs. A synthetic current-reason lock test confirmed that the locked learned clause was retained while other valid prefix clauses were deactivated. A false claimed RUP prefix was rejected before search.

The deactivation audit records the exact removed IDs and the locked/conflict IDs at each reduction. Tests verify no static, binary, locked or current-conflict clause was deactivated. Reproduce with test_solver_reduced.py; results are in solver_reduced_tests.json. No original solver_plus.py or currently running process file was modified.

## Benchmark scope

No real query was launched by this agent concurrently with the primary agent's existing90-second runs. The primary agent owns subsequent frozen-input comparisons. Both variants should include the same prefix-verification work when comparing total wall times: the reduced constructor performs that check internally. Report initialization, checking and search separately. A shorter watch list or more conflicts in a fixed interval is not by itself evidence of faster solving, and UNKNOWN still gives no numerical bound.

Future Lean export must choose literal parser fuel from the ACTUAL proof's maximum learned-clause length. Current later three-centre prefixes have clauses longer than the pointwise adapter's2048 fuel; the pointwise7621-step certificate remains unchanged and fits its documented bound. Reusing its fuel blindly for later exports would be incorrect.
