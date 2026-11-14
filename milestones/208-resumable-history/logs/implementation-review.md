# Review of saved-frontier implementation

Read `scripts/history_solver.c` and `scripts/continue_search.py`. No compiler, search, or software test was run. No saved-domain coverage defect was identified in the inspected C implementation. The wrapper implements the required whole-state replacement. One cancellation issue was reported separately to the main investigation and is described below.

## Limit frontier and ancestor bundles

The C limit check occurs at entry to `visit`, before propagation. It copies that call's entire domain vector into owned static storage and returns result two. Thus an entry limit retains every assignment represented by the call, including states that future propagation might refute.

The parent branch loop clears the current value from its `remaining` mask before invoking the child. If the child returns result two, the parent copies its own already-propagated domains and replaces the chosen variable by exactly that remaining mask, provided it is nonempty. The parent domain array is unchanged by child search because each child receives a separate copy. Earlier children have returned exhausted, the current child's pending regions retain its fixed branch value, and the ancestor bundle contains precisely the unvisited values.

The pending regions therefore cover the complete unrefuted portion of the input job. They are pairwise disjoint: at each unwind level, the ancestor bundle excludes the current value fixed in every descendant region. Every saved mask is a subset of the input job's corresponding mask. The solver returns immediately after a limit unwind, so it cannot subsequently modify a saved region or enter another branch before reporting it.

Static pending storage holds one entry-limit region and at most one bundle per ancestor. Every branch fixes a previously nonsingleton variable, so the depth is at most the number of variables. The allocated `NMAX + 1` entries suffice. Any unexpected capacity violation exits unsuccessfully rather than reporting exhaustion.

The wrapper checks every returned vector's dimension, nonempty masks, and coordinatewise inclusion in the input job. It also checks pairwise disjointness using a coordinate with disjoint masks. These checks support the intended representation, but do not independently prove coverage; that still relies on the native traversal argument and implementation.

## Unchanged constraints and lex inequalities

Each case copies the original model and permutation list, constructs a fixed constraint tail, and records their hashes. Every continued job sends that same tail, changing only its domain vector and resource budget. It does not renormalize the restricted domain vector or choose a new local orbit representative. The original global lex inequalities are therefore retained, and their fixed-prefix propagation remains sound inside arbitrary saved subproblems.

The model and engine pins are checked on resumption and again before a transition is committed. The base-history model and the geometric interpretation of the copied permutation list retain the separate obligations established in round 207. The continuation reader does not independently prove those geometric facts from the copied data.

## State transition and receipts

The authoritative pending frontier remains unchanged while a child process runs. A hard termination or nonzero exit records `NOT_COMMITTED`, asserts that the state file is unchanged, and returns without removing the input job. Malformed output, failed assertions, or failed file operations before state replacement likewise leave the old state as the committed record.

For a valid exhausted or limited result, the wrapper constructs one complete replacement state in memory. It removes the old job and inserts all returned regions in that single state. Reversing the insertion order makes the deepest saved job the next item popped from the end; this affects work order only.

The transition receipt is saved before the state replacement and contains the old state hash, input hash, model and engine pins, solver result information, and the new state hash. The `save` function writes a same-directory temporary file, flushes it, calls `fsync`, and replaces the destination with `os.replace`. Thus removal and insertion occur together as one entire-state replacement, addressing the loss window identified in the mathematical review.

An `ACCEPTED_TRANSITION` receipt can exist even if interruption occurs before its state is committed. Receipt status alone must not be treated as proof of commitment; the authoritative state and its linked receipt path/hash determine the committed history. The separately written `state-after.json` is an audit copy, not the queue authority.

This supports conservative recovery from ordinary process interruption under the intended single-writer operation. It is not a fully established guarantee against every operating-system or storage-power failure: the code does not synchronize directory metadata after replacement, and some auxiliary audit files are written without explicit `fsync`. The pending-domain cover is stored directly in the synchronized new state.

The lock-file creation uses an existence check followed by a write, rather than an exclusive atomic acquisition. The intended one-wrapper-at-a-time assumption should therefore remain explicit. This review does not establish a concurrent-writer protocol.

## Witness handling

For `FOUND`, the wrapper validates the assignment against the job domains, binary constraints, forbidden tuples, lex inequalities, and reconstructed full path. It writes the witness and changes the case status to `FOUND`, while retaining the old frontier. It consequently makes no exclusion claim about the remaining search region. This is the correct distinction from an exhausted job.

## STOP behavior and identified cancellation issue

The C process checks the local `STOP` file at nodes 1, 257, 513, and so on, in addition to its ordinary time and node limits. Detecting it uses the same covered-limit unwind. The check is not performed inside propagation, so cancellation need not be immediate. The wrapper's two-second grace interval can therefore end in a hard kill; the old pending job is then retained.

When the wrapper itself creates `STOP` for a resource or wall-time reason, its local `stop` variable records that reason. After a graceful covered return and state commitment, the wrapper returns `RESOURCE_STOP`, ending the batch. This path is sound.

In the inspected version, a manually created per-run `STOP` file is not read back into that local variable. C returns a covered `LIMIT`, but the wrapper sees `stop is None`, returns `CONTINUE`, and launches another job in a fresh directory without that file. Thus manual `STOP` checkpoints one invocation but does not reliably cancel the batch. This does not lose coverage or create a false exclusion, but it defeats batch-level graceful cancellation. Detect the run's `STOP` file or an explicit returned cancellation reason before deciding to continue if that is the intended user control.

## Native scope

The implementation maintains a native covering frontier under the reviewed pruning and unwind assumptions. An `OPEN` state proves no exclusion. An `EXHAUSTED` state supports exclusion only through the entire sequence of sound native transitions from the initial model. The generic Lean coverage lemmas do not verify those transitions, saved vectors, receipts, or executable behavior. This review inspected source only and makes no claim that a continuation run has completed or that a concrete native certificate has been checked by Lean.
