# Critical-context certificate review

The bounded audit found no blocker in the exact input, retained core, variable transport, packed proof representation, or generated source structure. The saved native certificate is complete. Lean clause interpretation, Lean proof replay, and the actual-snake theorem remain pending.

## Exact input and retained assumptions

The query uses direction word `012032`, normalized vertices `[0,1,3,7,6,14,10]`, resolution 12, and share cap 16. Its five internal count bounds are exactly

\[
(4,4),\ (4,4),\ (4,4),\ (5,5),\ (3,3).
\]

Reconstructing the deterministic encoding reproduced all 98,836 clauses, 13,856 variables, and the complete saved meanings, counters, tags, and vertex table. This reconstruction uses the pinned encoding implementation without constructing or invoking a solver. It verifies input identity; semantic soundness remains a separate Lean obligation.

All 11,869 core clauses equal the input clauses at their saved original IDs, preserving literal order and multiplicity. The original IDs are sorted, distinct, and in range. Every retained tag was checked against the input meanings. All five exact count bounds remain in the generated statement. The retained overflow clauses do not justify automatically dropping lower bounds or replacing this result with a count-free theorem.

The core includes 127 ordinary cycle exclusions: 90 squares and 37 six-cycles. Their literals identify distinct selected vertices whose induced subgraph has degree two at every vertex. No new cycle cut was appended to this query. The ordinary endpoint budget remains two, with no prescribed endpoint location or path parity.

## Native certificate and transport

The pinned native solver record reports exit code 20 and `UNSATISFIABLE`. The replay worker reports exit code zero and `PASS_COMPLETE_NATIVE_RUP_REPLAY`. Its saved result records 30,305 deductions, 1,754,767 references, and 396,942 derived literal occurrences. The receipt, worker output, input, core, original IDs, raw proof, trimmed proof, and replay implementation hashes agree.

This audit independently scanned every trimmed deduction for increasing original IDs, positive backward references to retained inputs or previous deductions, variable bounds, exact reference counts, and the final empty clause. It did not repeat unit propagation. The native propagation result remains the saved producer check.

The variable bijection was independently reconstructed: 5,707 active variables first, followed by the remaining counter variables, for 6,396 semantic variables. Every compact core clause and every generated raw clause agrees with that bijection. All 93 raw chunks have the expected lengths: 92 chunks of 128 clauses and a final chunk of 93. All retained tag rows and both packed variable-meaning payloads were compared with the saved original meanings.

The complete transport was independently compared without propagation:

- Every deduction's signed literals, original input-ID remapping, destination, ordered hint sequence, and packed binary payload agree.
- Last-use indices, slot reuse, and the preorder tree-key map were reconstructed.
- All 290 segment boundaries and all 10 checkpoint databases agree with the live clauses and their packed contents.
- The tree has height 14, uses 11,914 slots, and has 16,383 available positions. Proof words are 14 bits. The largest possible semantic literal word is 14,589, below 16,384.
- The final empty clause has original ID **190427**, tree key **4398**, and empty packed clause content.

The packed file contains 3,998,770 bytes. Its complete positive-hint propagation was checked by the pinned producer transport. This review checked the exact mappings, representation, and checkpoints independently; it did not run a second propagation replay.

## Generated semantics and preserved repair

All 97 generated semantic source hashes match the current plan, and the import order is valid. The generated scalar data retain resolution 12, cap 16, and all five exact bounds. The generator is the milestone-150 template with the intended input paths, module names, and cap changes. Both transport scripts likewise match their intended milestone-150 derivatives.

The corrected assembly uses

`AxiomsS S E window (centresOf window bounds) resolution cap`

and rewrites `centresOf` to `centresK` before applying the tagged-clause lemmas. This matches the generic model and the checked milestone-150 assembly. Its conclusion remains conditional on `Unsat cnf`. The original unchecked source and plan are preserved under `audit/semantic-source-v1`; their hashes match the repair record. This was a source correction before compilation, not a failed Lean proof attempt.

No milestone-153 object or accepted Lean receipt was present at the audit observation. The 97 expected axiom reports remain pending.

## Bounded pilot and actual-snake adapter

The newly prepared pilot has 34 uncompiled modules. Its source hashes and import order were checked. It contains 93 initial clause chunks and the first 2,095 deductions with 6,002 references, followed by its checkpoint. Its consequence is preservation of tree truth from a satisfying input assignment; it is not the full contradiction.

The emitter exactly matches the milestone-150 emitter after renaming and adding a requirement that full generation first read an accepted pilot receipt. The expected full layout has 137 modules, 290 segments, and ten groups. Neither full source generation nor a successful pilot check follows from the prepared source plan alone.

The separate `CriticalShareAdapter153.lean` contains three uncompiled theorems. Its statement carries count bounds explicitly. Its reverse case imposes the bounds on centre `r+(4-i)+1`, so the required chronological counts become `[3,5,4,4,4]`. The final proposed consequence retains an explicit `Unsat ShareWindow153.cnf` premise. No count-free or universal share-17 result is asserted.

## Remaining obligations and scope

Acceptance still requires the semantic checks, initial-tree pilot, entire Lean contradiction, checked count-aware coordinate/reversal transfer, and final composition. A graph update or a global bound is a further task.

The accompanying JSON contains the exact hashes and check results. The preceding pair-query/cycle review was verified unchanged. Only the two newly assigned audit files were written. No compiler, solver, full propagation replay, graph optimizer, process-control action, or Git operation was run.
