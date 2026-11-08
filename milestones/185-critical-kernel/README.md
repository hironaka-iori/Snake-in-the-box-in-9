# Round 185: permutation-invariant cap semantics

This round completes the request for one 15–25 minute round and then a pause. Pause after publication. Do not start round 186 without a new instruction.

The result is a Lean-checked generalization of the share-clause soundness theorem. The streamed critical floor-15 certificate lists fourteen threshold layers first and appends the fifteenth layer. The previous checker required a fixed order. The new checker accepts a permutation of the threshold pairs, with multiplicities preserved. Permutation preserves the number of true threshold terms; each corner contributes at most its physical integer share. All other local hypotheses remain unchanged.

The general counting, clause-soundness and refutation-composition implications passed Lean. The current dependency order has 200 modules, of which 98 are accepted. These contain generic proofs and exact constant data. **Zero of the 98 concrete clause batches has been checked.** Initial-database truth and the critical Lean contradiction remain incomplete.

## Exact input and proof boundary

The generated CNF is byte-identical to the round-183 dense input: 12,424 clauses, 5,342 proof variables and SHA-256 459cfa232e1c5fd55bd065db8dba50699103b612daaaf88b65636b77007687fa. Interpretation uses 5,906 variables, including auxiliary meanings needed to validate counters. No input clause was weakened or removed. The native refutation remains the separately replayed 52,489-deduction proof from round 183.

The generic checker has accepted dependency reports for cap_total, soundS and refutedShare_of_check. These are implications under structural and local-model conditions. They do not establish that the concrete input satisfies those conditions.

## Resource obstruction and preserved attempts

The existing limits were retained: 1 GiB free memory before a core Lean check, 256 MiB private memory and a 768 MiB free reserve. No heavy worker remains. Failed attempts and exact source snapshots are in logs/.

Splitting general proofs into individual lemmas and splitting raw clauses and tags into smaller data modules succeeded. Explicit small meaning trees also compiled. However, both isolated Share185.Counts and Share185.Totals still exceeded the memory limit. No structural theorem was accepted; the 98 dependent clause batches and final composition were not run.

Generated documentation fragments, tuple syntax and the Boolean-equality-instance proof were corrected before acceptance. Their failed logs remain. Superseded sources are retained; data/current-order.json specifies the current dependency order.

## Mathematical consequence

The round-184 profile (15,14,14,14) and comparison 42254m + 45L <= 9928453 remain unchanged. They yield conditional 234 using nonnegative loss. This round removes the general order restriction from the checker, but does not discharge the concrete local-share premise or any inherited graph premise.

The maintained project range remains 191–235, with the archived 235 proof's complete independent rebuild pending. The optimum, 196 and an unconditional improvement are unresolved.

## Resume point

1. Read data/completion.json and data/current-order.json.
2. Divide concrete counter and totalizer conditions into smaller proved components, including individual literal conditions where needed. Preserve the original local assumptions and exact dense CNF.
3. Finish the 98 concrete clause checks and Share185.Compose.
4. Check the compact critical contradiction in Lean and connect it to actual snakes using the existing geometric bridge.

Do not repeat the native solver, completed generic proofs or old share-18 replay. The older replay remains at 33,111 of 145,215 deductions and is separate. Inspect live process handles before resuming a worker. Keep the guards, hashes and failed attempts.

The existing D: manuscript and short explanation are updated in place and mirrored under paper/. Authors and hypersetup are preserved. Full manuscript review is due in round 186, after the pause.
