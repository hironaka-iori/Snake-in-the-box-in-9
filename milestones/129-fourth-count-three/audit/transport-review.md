# Independent transport and reduced-proof review

The transport and all requested complete proof replays pass. The expanded input, the direct-clause prelude, the original native-proof mapping, both core mappings and both selected core files agree with their independently reconstructed bytes. The first trimmed proof and both new native core proofs end in an independently verified empty clause.

The second core candidate has the fewest verified references: 3500 input clauses, 50082 deductions, 2628221 ordered references and 1695 active variables. This remains a propositional refutation of the restricted fourth-count-three input. The geometric input interpretation and Lean replay are separate obligations, and the fourth-count-at-least-four branch remains unresolved.

The frozen input review and its files were left unchanged. This audit imports neither the transport scripts nor their trimmer or replay helpers. It launches no solver or compiler and writes only its new audit source, JSON evidence and this report.

## Expanded input and direct-clause prelude

The expanded formula contains 112225 input clauses:

| Input family | Clause identifiers | Count |
| --- | --- | ---: |
| Original milestone-125 formula | 1–106348 | 106348 |
| Coupled pair counter | 106349–109211 | 2863 |
| Four new branch counters | 109212–112225 | 3014 |

The auditor reconstructs this concatenation from the saved original formula and the two counter records and compares every clause, literal and serialized byte. Variable identifiers remain unchanged, with declared maximum 10175.

The 235 direct clauses are absent from this trusted input list. They are derived next, at identifiers 112226–112460. Their original identifiers 106349–106583 are shifted above the expanded input; their clauses and ordered references are unchanged. Every one of their 132921 references names an original clause between 1 and 106348. The audit independently replays every direct-clause derivation against only those original inputs.

This distinction is essential. The direct clauses have original-input derivations. The coupled geometric counter and the branch counters are additional input families whose interpretation requires the relevant actual-snake inequalities and branch hypotheses. They are not claimed to follow from the original formula alone.

## Transport of the original native proof

The reduced input map was reconstructed independently by retaining the original clause identifiers except the recorded 4917 removals, then appending the 235 direct-clause identifiers. This exactly reproduces the saved 101666-entry map. The resulting clauses followed by the pair and branch counters exactly reproduce the native 107543-clause input.

For a native input identifier at most 101666, its reduced map selects either an original input or a direct clause. Original inputs retain their identifiers; direct clauses are shifted to 112226–112460. Native input identifiers 101667–107543 map to the added counter inputs 106349–112225. Every native derived identifier is shifted by 4917, placing its first possible value above the prelude at 112461.

The audit reconstructs and compares every line of `expanded.raw.lrat`: first the 235 prelude deductions, then all 90825 original native deductions with all 5779098 references mapped. Clause literals remain unchanged. All 17870 original deletion records are omitted exactly as recorded. This omission is sound for the verified ordered positive-hint deductions: retaining a previously proved clause does not change the unit-propagation validity of a listed reference. No extension to general RAT deductions is assumed.

The initial trimmed proof is an exact line subsequence of the expanded proof. Its 6131 input clauses are precisely the original expanded-input identifiers appearing in its references. The corresponding `core.cnf` is an exact serialization of those clauses. A fresh complete replay, using only those 6131 inputs, validates all 51547 deductions and 5174750 references and ends at empty clause 203285.

## New core proofs and selected inputs

The first core-only run returned UNSAT in 23.907 seconds on the 6131-clause core. The second returned UNSAT in 20.766 seconds on the first selected 3652-clause core. Their raw files, terminal records, input files, solver executable, scripts and logs match their saved hashes.

Both raw proofs were replayed in full, including deletions. Their trimmed proofs are exact line subsequences. Every local core input identifier maps through its saved ordered core list to an expanded-input identifier. Derived identifiers map above 112225 by subtracting the local input count and adding 112225. The auditor compares every serialized mapped line, including the complete ordered reference lists.

The selected input files are independently rebuilt from the expanded formula using exactly the used global input identifiers. Both mappings preserve signed literals and clause occurrences. Separate complete replays of the mapped trimmed proofs validate the selected certificates directly against those selected input sets.

| Verified proof | Inputs | Deductions | Ordered references | Active variables | Maximum clause length | Maximum references per step |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Initial expanded trim | 6131 | 51547 | 5174750 | 3164 | 58 | 1004 |
| First raw core proof | 6131 | 67822 | 3325713 | 3164 | 67 | 732 |
| First mapped selected proof | 3652 | 48718 | 2642674 | 1712 | 67 | 732 |
| Second raw core proof | 3652 | 71764 | 3496263 | 1712 | 62 | 784 |
| Second mapped selected proof | 3500 | 50082 | 2628221 | 1695 | 62 | 751 |

Here “active variables” counts the distinct identifiers appearing in the retained inputs or any checked derived clause, rather than the declared variable count. All five proofs retain original variable identifiers up to 10142; a smaller active count does not itself renumber them.

| Proof | Deletion records | Deleted identifiers | Maximum live clauses | Final empty-clause identifier |
| --- | ---: | ---: | ---: | ---: |
| Initial expanded trim | 0 | 0 | 57678 | 203285 |
| First raw core proof | 18961 | 65670 | 15289 | 73953 |
| First mapped selected proof | 0 | 0 | 52370 | 180047 |
| Second raw core proof | 18974 | 70575 | 15216 | 75416 |
| Second mapped selected proof | 0 | 0 | 53582 | 183989 |

Every deletion target was available when removed. Every deduction identifier was fresh and increasing, and every positive reference named an available earlier clause. For each proposed clause, the auditor negated its literals and required every listed reference to be unit or contradictory under the resulting assignment. Its final reference had to produce the conflict. The whole streamed-file hashes match the recorded hashes; these are complete replays rather than prefix checks.

The audit required at least 1 GiB available memory before starting. The observation was 3728121856 bytes. Proof text was streamed rather than loaded whole. The complete audit took 28.328 seconds.

## Useful reduction in the semantic input

The smaller selected core uses the following input families:

| Family | First selected core | Second selected core |
| --- | ---: | ---: |
| Original formula | 2549 | 2407 |
| Coupled pair counter | 0 | 0 |
| New first-count lower bound | 0 | 0 |
| New second-count lower bound | 0 | 0 |
| New fourth-count upper bound | 113 | 113 |
| New upper bound on the other three counts | 990 | 980 |
| Total | 3652 | 3500 |

These counts are obtained from the saved selected global identifiers and the independently checked input-family ranges. They show that the selected concrete semantic export can focus on the two new upper counters. The pair theorem and first-count restriction still justify the actual-snake implication that the other three counts sum to at most eleven. Their absence as counter clauses does not remove that mathematical dependence.

This reduction is specific to the checked selected cores. It is not a claim that the unused counters follow propositionally from the original input, or that all broader constraints can be omitted from an arbitrary search.

## Observed checker capacities

No Lean compiler error or generated-export failure was observed in this audit. The existing `LratFastO3k15` and `LratFastO4k15` source files were inspected directly. They use literal-parser fuel 255, hint fuel 4095 and 15-bit clause keys. The selected second proof's maximum clause length 62 and maximum 751 references per step fit those two fuel limits.

The export must still validate its variable remapping and actual clause-slot allocation. The source variants have literal offsets 3000 and 4000, while the saved unrenumbered variables reach 10142. A dense remapping of the 1695 selected variables can address that discrepancy, but its map must be checked. Likewise, using the original proof identifiers directly or keeping all 53582 selected inputs and deductions under distinct 15-bit keys would exceed the inspected key range. Slot reuse or a sufficiently wide checker requires its own verified allocation. This review does not assume which checker or allocation a future exporter will select.

## Scope of the conclusion

The complete native contradiction is now independently checked for the selected subset of the expanded input. There is no dependence on trusting the solver's UNSAT line, the producer's replay, or the trimming function. The original native proof, its transport, and both reduced alternatives remain saved separately.

The remaining work is to interpret the selected original and new counter clauses for actual snakes, export and check the chosen contradiction in Lean, and compose those checks with the fitting-window and fourth-count-three hypotheses. The input additions remain explicit geometric and branch assumptions. No contradiction of the fourth-count-at-least-four branch, universal six-count floor, or improved global length bound is claimed.

## Evidence and reproduction

`audit/audit_transport.py` prints a read-only summary. Supplying `--output` creates a new JSON file exclusively. The evidence records each proof's exact used input list, active variable list, replay statistics, complete-file hash, mappings and all source pins. Every pinned input is rehashed after the checks.

| Artifact | SHA256 |
| --- | --- |
| Independent auditor | `67b95a0ae6df7a219dba007c4b6171edafe2781e2431d19f674d24ab03f5e23c` |
| Audit evidence `data/transport-review.json` | `ff1f5727dbc8f7d46f333a2f82005a4683fc94747d0a68f02ec2b287fe2d1fe5` |
| Expanded input | `3dafbc7918bd0e7cf0f4ef10ed89778fa55641d0591946d26d5f326ac5ebc1c7` |
| Expanded mapped proof | `56549a115cc6025098c3d6f5a7c4fa5640ccb6a541472e81333935de74bed4dc` |
| Initial expanded trim | `39e61b20561017f60bacebd37feef3d700e96e8ea5cb970d5b9ee89755935e53` |
| First raw core proof | `c098a8fe3c2054e3030f8d604ed52f4092996c750766c13edff44586b930cc32` |
| First mapped selected proof | `31933c9d3f4893a7e1d4cedb59bc41cd3b871cc066f2b70cf84a847be0930a17` |
| Second raw core proof | `9a71db0ab75a4533c8d51172c4a18c5272c26e2d90c1e2bb51ca43bf9779cf0d` |
| Second mapped selected proof | `82349c0f333ffb62b6817273aef142680b2889e9690ea7a7b8d63d65223e00cc` |
| Second selected core input | `fe48dadc239bdce3f3219bf5391ab576ab59cf04aa8625e1e33b56ecc51de281` |

The audit completed at 2026-11-03 07:11:52 UTC. No substantive transport or proof-replay defect was found within this scope.
