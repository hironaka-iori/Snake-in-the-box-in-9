# The exact reference list suffices

The graph tests a fixed list of 1,378 reference patterns. Suppose every pattern
in that list is impossible in its stated local model. This is the remaining
reference-refutation assumption; the present argument does not prove it.

Take any fitting nine-direction window of an actual snake. For each reference
pattern that fits inside it, the assumed local refutation rules out both the
forward pattern and its joint direction-and-count reversal. The existing
length, count and coordinate-normalization lemmas justify these applications.
Hence the window passes the reference filter. The other three filter families
and both history-compatibility conditions already hold independently of the
reference catalogue. The window therefore passes the unchanged full filter.

The checked graph-coverage result places that window in the graph with its
complete direction, history and count key. Applying the graph's potential
inequality to each such row and telescoping gives the existing inequality

$$P(m-8)\le W+R.$$

Here the notation has its existing meaning: $m$ is the number of snake edges,
$W$ the total graph weight, $P$ the potential slope and $R$ its range bound.
The total-weight budget is unchanged:

$$W+4200m\le1098960.$$

For $m\ge9$, the two inequalities give

$$(4200+P)m\le1098960+8P+R.$$

The completed profile has $(P,R)=(483,551)$ and gives $m\le235$ under its
explicit reference and complete-graph premises. The conditional profile has
$(P,R)=(496,602)$ and gives $m\le234$ under those premises and the same five
local share assumptions as before. The case $m<9$ is immediate in both bounds.

Lean checked all five implications in this chain. No definitions were added.
The exact reference union, the complete graph inequalities and the five
conditional share claims remain distinct obligations. A partial graph check
cannot replace the complete graph premise.

## Which contributor proofs are needed

The pinned contributor wrappers identify one exact source entry for each
selected reference key. A direct selection uses 732 entries from the R4
catalogue, 635 from K6 and 11 additional entries from R4b. The selection checks
the literal key, its index, the semantic proof name and the refutation proof
name. It needs 1,378 distinct proof roots. The three full source catalogues
together reference 1,383 distinct roots, so only five roots are omitted.
This count is not a runtime estimate or a new combinatorial bound.

All selected generated semantic source files are present at the pinned Git
paths. The 1,378 generated refutation source files are absent at those paths.
The closed wrapper statements and historical Linux logs therefore cannot be
imported as freshly checked local proofs. Their missing refutation roots must
be recovered or regenerated and checked, with their exact dependencies.
This is a statement about the pinned Git paths, not a whole-machine absence
claim or a claim that the underlying proof data have been lost.

The new argument makes the required list explicit and avoids reconstructing
the two larger catalogue propositions. It preserves every reference test used
by the graph, every accepted edge, both potential caps and the full charge
budget. It establishes no smaller numerical bound by itself.

## Current status

The maintained project interval remains $191\le a(9)\le235$ edges. The 235
upper bound retains the contributor's archived evidence and pending complete
independent rebuild. The target 234 and the exact optimum remain unresolved.
The active milestone 104 batch continues its complete graph certification.
Its live record is authoritative for current progress; this milestone stores
an immutable process-verified observation.

The manuscript remains revision 96. The scheduled full revision at 106 should
present this argument with ordinary notation and explicit remaining premises.
The original case7302 target 20 replay remains stopped and unchanged; a target 18
proof needs separate sources and evidence.
