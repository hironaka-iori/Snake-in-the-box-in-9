# Independent SolverPlus review

No valid-input soundness bug was found. The original solver.py was not changed by this review.

## Code audit

Binary clauses (a OR b) are stored as the two implications not-a=>b and not-b=>a, with their original clause IDs as reasons. Extraction occurs only after Base has completed permanent root propagation and watch rebuilding. Root-satisfied clauses can safely be omitted; root assignments are never backtracked. New learned binaries use the same implication path. Initial watch lists remove the extracted binaries, avoiding duplicate processing.

Circular scanning visits every one of the n-2 nonwatched positions before concluding no replacement exists. The remembered position only changes traversal order. Clause literals and IDs remain intact.

Literal minimization keeps the asserting literal, tries only lower-level literals and accepts a deletion only when the reason-DAG can explain the conflict from the remaining candidate assumptions. It then recomputes the backtrack level. Crucially, all resulting learned clauses are checked by the separate RUP verifier. No clause deletion or unchecked inprocessing was added.

Restart modes and seeded activity ties change search order only. The Luby sequence was independently checked. A timed-out SolverPlus object remains single-use, so an interrupted binary propagation list is never silently resumed from an advanced qhead.

## Independent regression evidence

All48 configurations passed: binary/circular/minimize enabled or disabled, three restart strategies, seeds0 and17. Each ran329 targeted, independently generated random mixed2/3/4-CNF, and pigeonhole cases, for15792 solves. Small formulas were compared against exhaustive enumeration. Every SAT assignment was checked on the original caller clauses, the caller clauses were verified unchanged, and every learned proof clause was checked even on SAT outcomes. Totals:67531 RUP steps and615097 hints. This test suite completed in9.10seconds; this is testing cost, not a Q9 speed comparison.

Explicit PHP7-into-6 coverage with all features enabled exercised real binary propagation, minimization and all restart modes. The three runs removed1571,1436 and1073 literals, performed4,6 and1 restarts, and each ended with an independently checked UNSAT proof.

A forced timeout exactly at the8192nd binary implication visit returned UNKNOWN and rejected a second solve call. A conflict-budget UNKNOWN run retained a valid one-step/five-hint proof prefix without an empty clause. UNKNOWN is not interpreted as infeasibility.

Artifacts: test_solver_plus_independent.py, solver_plus_configs.json, solver_plus_independent_results.json, solver_plus_coverage.py/json, solver_plus_timeout_controls.py and solver_plus_timeout_results.json.

These tests support using the variants for checked experimental searches. They do not prove that a strategy is faster, finish any Q9 query, or establish a new snake upper bound. Actual Q9 runs still need independent whole-prefix replay and exact SAT-model decoding.

## Real portfolio merge and continuation audit

All12 actual six-solve-second portfolio tails were independently replayed against their original frozen formulas. The merge leaves hint IDs in the shared initial CNF/prefix unchanged and adds the accumulated previous-tail length only to IDs naming the current tail's new clauses. This is the correct translation. I also checked the complete combined proofs from the original geometric/rule CNFs, and verified those CNFs exactly equal the original experiment sources.

The independently reviewed round-one continuation snapshots contain51,736 steps/4,229,516 hints for0120 and48,254 steps/4,132,057 hints for0123. Both have no final empty clause and remain UNKNOWN. The original frozen prefixes were41,490 and40,021 steps, respectively. Exact hashes and each tail's counts are in portfolio_results/independent_review.json. Continue-from-merged reconstructs logical state from the strengthened clause list and checks every new proof tail; it restores no unfinished trail.

A provenance hardening recommendation is to record the frozen-prefix SHA256 as well as its clause count in each portfolio receipt. Current complete RUP replay against the actual shared prefix already protects mathematical soundness, but a length alone is not an exact identity check. Also, future merges should stop when a tail reaches an empty clause rather than append later tails and potentially obscure the final-empty status flag.

The performance data show no uniform winner:0120 Luby produced1391 conflicts versus1126 baseline, whereas0123 baseline produced1123 and exceeded all enhanced variants. Conflict counts measure search activity, not proof progress or solved instances. All runs are UNKNOWN, so these measurements establish neither an overall speedup nor a new upper bound.
