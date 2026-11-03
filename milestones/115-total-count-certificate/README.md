# Milestone 115: concrete count semantics and distinct-direction windows

The five-count proof for `012310` has been reduced and independently
replayed. Lean now checks its concrete clause interpretation, including
the sum counter and cycle exclusion. The complete contradiction export
passes native simulation, and its sequential Lean batch is running.
The final actual-snake theorem remains pending until that batch finishes.

The selected reduced certificate has 287,753 deductions and 16,816,989
propagation hints, down from 358,464 and 22,088,504. Its complete export
contains 1,396 modules; the final actual-snake composition makes 1,397.
The first contradiction group passed Lean before the batch was launched.
Generated modules do not count as checked modules.

The new mathematical candidate concerns six distinct consecutive
directions: their five internal counts sum to at least 23. Native tests
reject totals at most 22 after five directly validated cycle exclusions.
A verified local forest attains 23, with counts `(6,3,6,2,6)`. This forest
has six components and is not a complete snake. The UNSAT certificate
and corresponding Lean theorem remain pending.

Read [the mathematical note](mathematical-note.md),
[the frozen checkpoint](data/checkpoint.json), and the reviews in `audit/`.
The graph experiments improve the completed-floor finite mean to
`6309/13`; the conditional mean remains 496. Integer comparisons remain
235 and conditional 234. These experiments still assume unproved local
rules and do not establish a new global bound.

## Reproduction and live work

Large proofs and both generated source trees are retained locally and
also stored in verified lossless archives. On a fresh checkout, run
`scripts/verify_saved.py --restore-archives` before compiling. The source
bundle is split into ordered parts smaller than GitHub's file-size limit.
Restoration validates every member and never replaces different bytes.

`data/total-plan.json` pins the complete export. `scripts/run_batch.py`
checks its dependency order and then `ActualTotal115`, preserving exact
attempts and receipts. Inspect `data/batch-progress.json` and verify its
live process before restarting anything. Milestone 104 also remains an
independent running verification batch. Permit at most one additional
compiler alongside that batch.

The archived checkpoint is a dated observation. Later receipts and
progress files can change as the running batch completes. The frozen
manifest deliberately excludes live process records and logs; it records
immutable snapshots and the completed receipts available at capture.

Paper revision 106 is unchanged; the next full revision is 116. There are
no new mathematical definitions. The maintained interval remains
191 through 235 edges, with the contributor evidence and pending complete
independent rebuild distinguished in the handover.
