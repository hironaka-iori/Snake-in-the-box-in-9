# Milestone 147: complete clause interpretation for the 012301 share target

The mathematical clause interpretation is complete. The final contradiction
and the application to arbitrary snakes remain pending. No new global upper
bound follows from this milestone.

## Target and completed implication

The target is the existing five-centre, resolution-12 share floor of 16 for
direction pattern 012301, with all five count ranges equal to [0,21]. The
Boolean instance assumes share at most 15. It uses the existing radius-four
local path and endpoint conditions, including acyclicity. The original
instance contains 92,656 clauses; its retained core contains 12,977 clauses.
Six clauses exclude induced eight-cycles.

All 102 clause modules now have accepted Lean receipts. The six cycle clauses
follow from the existing acyclicity condition; they introduce no additional
eight-cycle hypothesis. The original clause order, variable meanings,
counters and totalizers are preserved. Only imports were reduced relative
to the prepared sources in milestone 146. The six generic project modules
were freshly checked from their saved sources.

The assembly proves that every assignment satisfying the local assumptions
and share cap gives a satisfying assignment of the exact retained core.
Consequently, a contradiction of that core would exclude share at most 15.
This implication is checked; its contradiction premise is still open in
Lean. There are 113 accepted modules and 111 axiom reports in this part.

Evidence: [semantic completion](data/semantics-completion.json),
[independent interpretation review](audit/preserved146-review.md).

## Replay progress

The independent executable replay checks all 285,541 deductions and
31,017,505 propagation references. The renamed and packed proof preserves
every literal and reference. It ends with the empty clause at original
identifier 647093, stored at tree key 11657. This computational replay alone
does not complete the Lean contradiction.

The checked 36-module pilot connects the entire original core to the initial
proof tree and verifies 1,030 deductions, 6,004 references and a complete
checkpoint. Its 15-bit tree accommodates all 17,523 reusable proof slots.

The larger test checks the first 32 segments, their 8,653 deductions and
195,344 references, and the transfer to the next checkpoint. All 11 added
modules pass. Thus 47 of the 1,789 generated replay modules are accepted at
this saved checkpoint. The full replay has 5,089 segments in 160 groups.
Prepared source is distinguished from accepted proof throughout the records.

Evidence: [pilot completion](replay/data/pilot-completion.json),
[first group](replay/data/first-group-completion.json),
[full source plan](replay/data/full-source-plan.json),
[dependency order](replay/data/full-execution-plan.json).

The immutable first-group snapshot records the published boundary. Later
live progress belongs to `replay/data/full-replay-progress.json`; it may
advance beyond this milestone without changing the snapshot. Inspect the
lock and actual processes before resuming. Do not launch a duplicate driver.

## Consequences for the bound

The maintained project interval is

\[
191\le a(9)\le235.
\]

The upper endpoint uses the inspected contributor theorem and archived
dependency audit. A complete independent rebuild remains pending. The
conditional 234 profile retains its local-share, reference and potential
certificate premises. The optimum and the conjectured value 196 remain
unresolved.

The immediate next task is to finish this exact contradiction, then compose
it with the checked clause interpretation and the coordinate and reversal
arguments for actual snakes. This target must remain part of the joint
012032, 012301 and 012340 analysis. Milestone 145 proved that raising only
the latter two floors to 16 cannot bring the existing comparison below 235
when its other weights and eleven-cycle remain fixed. The proposed 012032
floor changes the eleven-cycle total, so that obstruction does not exclude
the full conditional profile.

The completed 1,397-module count-sum proof for 012310 is separate and must
not be restarted. The preserved 012034 share-18 proof is also separate: its
initial tree and prefix are checked, while its full replay is unfinished.

## Verification and recovery

Accepted receipts pin source, compiled object, compiler output, checker
snapshot and dependencies. Accepted axiom reports contain only the standard
Lean axioms `propext`, `Classical.choice` and `Quot.sound`, or subsets of them.
The Lean 4.19 standard library is trusted; compiler and direct standard
library objects are pinned. All project generic modules used here are
freshly compiled.

Each compiler runs alone, with a 3 GiB private-memory limit, a 768 MiB
free-memory floor and at least 1.5 GiB free memory before launch. Small
generic modules use one thread and an 8 MiB stack. The earlier memory
failures and the rejected `-M` option are retained. No failed run is counted
as accepted evidence.

Large immutable inputs and all generated replay sources are saved in seven
archives with per-file hashes. The originals remain local. Use
`scripts/restore_archives.py` on a fresh checkout to restore only missing
files after verifying every archive and destination. Compiled objects are
local build products and are not published as replacements for proof source.

The open paper and repository mirror contain the same targeted verification
update. Authors, preamble, statements, displays and existing definition are
preserved. Static source checks pass. The built-in compiler failed before
TeX processing because of its Windows helper configuration; no new PDF or
visual-layout check is claimed. Last full paper revision: 146. Next: 156.

Goal ACTIVE. This milestone makes progress and does not establish optimality.
