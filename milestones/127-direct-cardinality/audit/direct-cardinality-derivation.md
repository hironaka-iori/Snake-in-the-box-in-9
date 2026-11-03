# Direct clauses for the existing six lower bounds

This review concerns how the already established lower count bounds are
exposed to the solver. It establishes no new local count floor and excludes
no snake. The generic source is `lean/DirectCardinality127.lean`.

## Mathematical equivalence

For a finite set of $n$ corner positions and $1\le k\le n+1$, at least
$k$ positions are absent if and only if every set of $k-1$ omitted positions
leaves at least one absent position outside it.

In the forward direction, all absent positions cannot belong to a set of size
$k-1$. In the converse direction, if there are at most $k-1$ absent positions,
enlarge their set to one of size exactly $k-1$. This is possible because
$k-1\le n$. Every position outside that set is selected, contradicting the
corresponding clause. The proof reuses the existing finite-set extension lemma.

For $k\le n$, the lower bound is also equivalent to having at most $n-k$
selected positions, because the selected and absent positions partition the
set. This is the inequality represented by the existing tagged lower counter.

The range restrictions matter. For $k=0$, the lower bound is automatic and
there should be no clauses. The displayed omitted-set schema would instead
require an absent position because natural subtraction gives $k-1=0$.
For $k=n+1$, it has one empty clause and correctly expresses impossibility.
For $k>n+1$, no omitted set of size $k-1$ exists, so the schema is vacuous
despite the impossible lower bound. The theorem states the necessary range.

## Concrete clause family

At each internal centre, two path directions leave seven free directions and
$\binom72=21$ corner positions. The existing six intervals are

$$
([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]).
$$

The direct clause contains the negative selected-vertex literal for every
position outside the omitted set:

| Centres, in path order | Lower bound | Omitted positions | Generated clauses | Width |
| --- | ---: | ---: | ---: | ---: |
| 1, 3, 5, 6 | 1 | 0 | $4\binom{21}{0}=4$ | 21 |
| 2 | 2 | 1 | $\binom{21}{1}=21$ | 20 |
| 4 | 3 | 2 | $\binom{21}{2}=210$ | 19 |

The schema therefore generates 235 clauses, with 4494 literal occurrences and
no new variables. This counts generated clauses per centre; global distinctness
of all concrete clauses requires checking the actual corner lists.

The inspected `TaggedEncoding.build` calls its at-most counter on positive
selected-corner literals with threshold $21-k$ for each lower bound $k$.
Here the thresholds are 20, 19 and 18. The new negative clauses express the
same count condition. The generic complement theorem establishes this logical
equivalence, without inspecting concrete counter registers.

## Multiplicity

The Boolean specialization maps positions to corners without requiring that
map to be injective. Repeated corner values remain different positions and
retain their multiplicity. This avoids replacing the six-centre total's 126
occurrences by its 100 distinct vertices. The 235 clauses concern individual
lower bounds and do not replace the total-at-most-22 counter.

Contracting identical literals within one disjunction preserves its truth
value. It does not justify removing repeated positions from the cardinality
domain. The complete family of omitted-position clauses gives the equivalence.

## Proof integration limits

Logical equivalence does not by itself establish reverse-unit-propagation
derivability from the saved 106348-clause input. Every concrete prelude clause
must receive that separate check with the original literal numbering.
The new clauses occupy identifiers 106349 through 106583. Each may depend
only on original clauses or earlier verified additions. Subsequent proof
identifiers must continue above this range.

Combined trimming and replay must use the original formula with 106348 trusted
inputs. Treating the 235 new clauses as unexplained trusted inputs would omit
their required derivation. Neither this equivalence nor a successful prelude
provides a final contradiction.

The actual-snake theorem from milestone125 supplies the six intervals under
the fitting canonical pattern $0120324$ and total at most 22. The full-cube
search remains unresolved. This generic lemma implies neither impossibility
of that case nor a universal six-count floor of 23.

## Verification status

The isolated Lean check passed in 6.890 seconds with five axiom reports:
the direct-clause equivalence, complement-count equivalence, Boolean position
specialization, omitted-set count and concrete clause arithmetic. The first
four use only `propext`, `Classical.choice` and `Quot.sound`; the concrete
clause arithmetic uses no axioms. The source introduces no definition.

The first attempt correctly launched no compiler because the resource gate
was closed. The successful attempt started only after a fresh inspection
found 6660108288 available physical bytes and exactly two other Lean
processes, satisfying the agreed 1.5 GiB threshold. The source, checker,
resolved direct imports and toolchain pins were unchanged across the run.
This is a check against the existing compiled Mathlib dependencies, not a
fresh reconstruction of the full library.

The successful record is
`logs/direct-cardinality-1793686604453734400/record.json`. Its directory
contains the compiler log and exact source/checker snapshots. The object is
`build-independent/DirectCardinality127-1793686604453734400.olean`.

SHA-256 pins:

- Source: `12b6b2dc451048018f8ea7ac8451db818bb46eb5a2b519d8aa9f9e518b29051a`.
- Object: `6e0da6a6229ffd192c3978ec87cbf62237417dfeae8b5a10c1776c5c31a89bbc`.
- Compiler log: `95948006318344b40634c9dd75482bd27141c65652b91c3fb799aa121e039cdc`.
- Checker: `b8ae56ab999710c1071e309365fe1a66a19429c7e3a101cf75cd9642d4aa4c90`.

A separate exhaustive sanity check covered 4097 combinations of set size,
threshold and Boolean assignment for $0\le n\le8$ and $1\le k\le n+1$.
Every case agreed with the equivalence. The $k=0$ and $k>n+1$ failure cases
were also exhibited directly. These checks supplement the generic Lean proof.

The existing 104, 115 and 122 drivers and their outputs have not been modified.
