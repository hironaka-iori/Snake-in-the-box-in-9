# Count-free share 16 on 012032: certificate and remaining proof

Let \(x_0,\ldots,x_m\) be an induced path in \(Q_9\). For a fitting
six-transition window with directions 012032 after coordinate relabelling,
in either orientation, the target is

\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge 16.
\]

The notation is the existing resolution-twelve empty-square share. No new
definition is needed. The canonical vertices are 0,1,3,7,6,14,10.

## Why the extra count condition is unnecessary

The first search imposed share sum at most 15 and
\(\alpha_{r+2}+\alpha_{r+4}\ge 10\). The original count-free input has
92,640 clauses and 11,378 variables. The pair constraint appended 508 clauses
and 174 variables. It counts 42 corner occurrences at 37 distinct vertices;
their multiplicities were preserved.

The retained contradiction contains 13,655 input clauses, all selected from
the original 92,640 clauses. None of the appended clauses or new variables
occurs in its retained core or derived deductions. An independent audit
reconstructed both complete inputs and checked every selected clause.

The reduction is elementary. A contradiction derived using only clauses
of the original input is already a contradiction of that input. A
satisfying assignment of the original input would satisfy every retained
core clause and therefore every valid derived clause, including the empty
clause. Unused variables in the core file's header add no constraint.

The independent numerical replay validates all 58,182 deductions and
5,350,080 ordered propagation references, ending at original empty-clause
ID 205425. Its 4,406 derived variables all occur among the 5,442 core variables.
The retained geometric cuts are 246 ordinary four-vertex cuts and 69 ordinary
six-vertex cuts. No additional cycle exclusions are needed.

## Checked implication and unresolved contradiction

The 112 new Lean module checks cover the exact core,107 clause shards, their
assembly and the coordinate/reversal consequence. They establish the
following implication: if this exact core is unsatisfiable, every fitting
actual-snake window of either canonical orientation has share at least 16.
The implication has no extra pair, parity or endpoint-location premise.
Its count bounds are the universal interval 0 through 21, and its endpoint
budget is the ordinary limit of two.

The module receipts contain 112 axiom reports, restricted to the usual
Lean axioms. Generic local models are reused from 147 and coordinate and
reversal helpers from 148 with pinned source, object and dependency records.
The 148 dependency closure includes one previously checked data object;
the record does not claim a fresh rebuild of that object.

This implication alone does not discharge its unsatisfiability premise.
The complete numerical proof was renamed and packed with an independent
replay preserving signs, literal order and multiplicity, ordered hints,
and live-clause slot ownership. The resulting replay has 878 segments,
13,655 slots, a tree of height 14 and 14-bit words. The 38 module pilot sources
cover the initial-tree connection and a prefix of 2,169 deductions with
6,151 references. Those pilot sources remain uncompiled. Full replay and
composition with the checked implication remain required.

The numerical transport is smaller than the current 012301 replay in
segment count. No comparable Lean runtime measurement exists, so no
runtime improvement is asserted.

## Relation to the upper bound

Milestone 149 shows why weakening the 012032 floor to 15 and adding uniform
occurrence credit cannot succeed on the original fixed graph. The present
certificate instead supports its original floor 16 target. Completing it
would discharge one local premise of the conditional 234 profile. The
other local floors,1,358 remaining reference refutations and complete
potential certificate would still be necessary.

A weaker fallback had allowed one unit of share loss on each actual
low-pair occurrence. Under its unproved local hypotheses, the existing
occurrence bound would spend 24 of the 30 units of margin at length 235. This
arithmetic route is recorded separately in `audit/actual-event-bridge.md`.
The stronger count-free certificate makes a new implementation of that
fallback unnecessary at this stage.

The second numerical search, count-free cap 14, also passed complete
independent replay:57,042 deductions and 4,799,567 references. Its exact
evidence is retained, but a second Lean pipeline is not selected.

No new global bound follows from this checkpoint. The maintained
interval 191--235 retains the contributor independent-rebuild limitation.
The value 196 and the optimum remain unresolved.

## Continuation

The same 147 coordinator remains responsible for the active 012301 full
replay. Revalidate its identity and progress; do not launch a duplicate.
On completion, audit every receipt and check the already prepared 148
composition. The next bounded new 012032 task is the initial-tree and prefix
pilot; it must run without overlapping another Lean compiler. Generate
the full replay only after that pilot passes. Preserve failed outputs and
the exact source and dependency hashes at each step.
