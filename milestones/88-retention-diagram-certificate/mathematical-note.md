# Forbidden boxes and a finite coverage certificate

A six-count code represents a vector in \(\{1,\ldots,6\}^6\).
The symbol six retains its earlier meaning as the interval \([6,21]\)
for the underlying singleton count. This note concerns the encoded vector.

## Forbidden boxes

A *count box* is a product

\[
B=[l_0,u_0]\times\cdots\times[l_5,u_5]
\subseteq\{1,\ldots,6\}^6.
\]

A rule witness identifies a particular reference, short, interval or history
exclusion, its placement and its orientation. A valid witness certifies that
every vector in the box triggers that exclusion. The required checks are:

- A reference witness fixes the relevant coordinates to the reference symbols.
- A cap witness bounds the tested coordinates above by the forbidden caps.
  A sum witness bounds the sum of their upper endpoints and keeps every
  tested upper endpoint below six.
- An interval witness places every tested box interval within its forbidden
  interval, respecting reversal.
- A history witness matches the remembered signature and bounds its tested
  coordinate above by two.

The checked implication is that a bounded code passing numeric retention
cannot belong to a box with a valid witness. The reference case uses a
separately checked reconstruction of the code from its six digits and a
slice-encoding identity. This statement applies to arbitrary bounded codes.
Its specialization to snakes uses the earlier two reference-catalogue premises.

## Coverage by a six-way tree

A certificate reads count coordinates in order. A branch ends when the
membership diagram accepts every remaining suffix, or when a validated box
contains every remaining suffix. Otherwise the branch splits into all six
possible values of the next coordinate.

The checker records the fixed prefix. A box closes a branch only if it
contains all fixed prefix values and has lower bound at most one and upper
bound at least six in every remaining coordinate. Thus a valid certificate
proves that every vector is either accepted by the diagram or lies in one
of the listed boxes. A code passing numeric retention avoids those boxes,
so it must be accepted by the diagram.

This implication and its actual-snake specialization are Lean-checked.
The finite witness-validity and certificate-check equations are explicit
premises until the corresponding concrete data are checked.

## Sharing the finite work

The computational reconstruction verifies all 505 base direction cases and
the three history modifications, recovering all 791 compatible blocks and
4,947,008 retained rows. The 37,084 incompatible blocks are empty.

Across the base cases, 573,640 raw box occurrences reduce to 543,829 after
duplicate removal. The maximum-uncovered greedy construction and a redundancy
pass retain 356,548 occurrences, using 2,637 distinct geometries. Each retained
occurrence has a private omitted code within that final cover; this proves
irredundancy of the chosen cover, without a minimum-cardinality claim.

The more useful reduction groups contexts by their saved count-code set.
For every one of the 127 classes, the intersection of the available box
geometries across its contexts still covers the entire omitted set.
Pruning these common covers yields 82,659 class-box occurrences. A geometric
coverage certificate can consequently be shared within a class after each
context's rule witnesses have been checked. The intersection and coverage
claims in this paragraph are currently computational results.

## Concrete pilot and outstanding scope

The first generated certificate uses direction ID zero and history ID zero.
It contains 375 witnessed boxes and a tree with 723 distinct nodes. Its
expanded traversal visits 11,869 nodes. Independent replay checks all 46,656
codes and finds exactly 6,123 accepted codes. Lean subsequently checked all
375 witnesses, the coverage-tree equation, and the resulting retained-code
membership theorem. These three concrete checks took 92.594 seconds. The
coverage equation has no axioms. The saved generation receipt records its
earlier pending stage; the later proof receipt records successful validation.

This gives a precise finite coverage lemma: for the specified direction and
history, each code below \(6^6\) that passes numeric retention is accepted
by the saved diagram root. The generic argument supplies the same conclusion
for any context once its witness and coverage equations have been checked.

One checked pilot does not establish coverage for all contexts. The full
finite certificate, its identification with the saved retained rows and
endpoint columns, edge-weight interpretation and complete potential proof
remain necessary. No upper-bound improvement is claimed here.
