# Milestone 78: numeric history transitions and actual state sequence

Four modules passed Lean 4.19.0, with 29 printed theorem audits. The result
connects the history selector and the five-count state encoding to an arbitrary
actual snake. The global interval remains 191 through 235 edges. The target 234
retains the six pending local share targets, retained-edge and credit
interpretation, and complete potential replay.

## Selector theorem

The graph builder considers nonempty dictionary suffixes of the stored history
followed by the new direction ID. It selects a maximum-length candidate and
uses index zero if there is no candidate. The new proof checks a scan in
increasing index order, replacing its current choice only for a strictly
longer candidate. The selected index is in range and denotes the longest
dictionary suffix. Two equal-length suffixes are equal, so dictionary
distinctness rules out different maximizing indices.

The empty-candidate guard is retained. The proof also identifies the suffix
predicate with the builder's explicit length guard and final-slice equality.
The scan theorem and the existing history decoder give

\[
q_{r+1}=\operatorname{next}(q_r,d_r),
\]

where the actual history is obtained by reading the actual direction IDs from
the start. The equality of total functions holds even for arbitrary symbol
values; valid snake-window bounds are imposed when interpreting an ID as one
of the builder's 505 recorded extensions.

The exact three Python selector assignments were extracted from the builder
and checked on all 37,875 input pairs. Every result equals the strict scan;
2,363 updates are nonempty and 791 pairs satisfy the source compatibility
condition. Every such pair satisfies the target compatibility condition.
This executable comparison is separate from the Lean theorem about the scan;
the Python interpreter is not encoded in Lean.

## Actual states and endpoints

The count identity from the existing source was extracted and checked again.
It identifies the geometric singleton-square count with the computable core
count and supplies positivity. Truncation therefore gives symbols in \([1,6]\).

For a snake with \(m\ge9\) edges, the state at position \(r\) contains its current
eight-direction shape, its numeric history, and the base-six encoding of the
five counts at \(r+3\) through \(r+7\). Its index is below 1,601,856. The six-count edge
code is below 46,656, division by six selects its first five counts, and reduction
modulo 7,776 selects its last five. The entering count is the final base-six digit
plus one.

The checked source and target formulas agree with consecutive entries of one
actual state sequence. There are \(m-8\) encoded steps and \(m-7\) states, including
the terminal state. Both history-shape compatibility conditions hold. These
facts establish an encoded sequence of endpoints; they do not assert that its
steps have survived every filter in the retained graph.

## Evidence and remaining gap

`data/*-audit.json` records each successful source, object and log hash and its
printed axioms. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The exact successful milestone77 support and additional count support are
hash-checked. Their entire inherited dependency closure is not rebuilt.
`audit/` contains independent source reviews and the executable selector audit.

The next task is retained-edge membership: prove that every actual triple of
direction ID, six-count code and history passes each reference, recovered-rule,
history and interval exclusion. Then identify its retained array index and
interpret every credit through all compatible eleven-direction words. Credits
on the same five centres combine by maximum. Full potential replay and the six
local share targets remain before the conditional 234 argument can become a
global theorem.

Case 7305 remains under its existing completion driver until a terminal result
is observed. Inspect the saved checkpoint and actual process before any restart.
Partial refutation checkpoints do not establish its final local share theorem.

## Reproduction and preservation

From `E:/Snake-in-a-box`, use the installed Python runtime with `-X utf8`.
Run `scripts/check.py` on `IndexSelector`, `NumericTransition`, `CountGeometry`,
then `StateWalk`. Run `audit/check_builder.py` for the exact Python comparison.
`scripts/prepare_count_bridge.py` records the source of the reused count proof
and its additional inherited support. The checker records its search paths.

Build objects remain local. Sources, logs, audit receipts and the handover
checkpoint are preserved with exact-byte attributes. The paper remains
revision 76; no paper edit or new PDF compilation is part of this milestone.
