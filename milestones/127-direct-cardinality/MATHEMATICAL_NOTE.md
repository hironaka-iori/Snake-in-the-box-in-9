# Direct clauses for the unresolved six-count window

The working hypothesis is that every fitting window with direction pattern
0120324 has six internal singleton counts summing to at least 23. This would
exclude the sum-22 edge on the saved conditional comparison cycle. It would
not by itself establish a new global upper bound, since replacement cycles
and the other stated proof obligations must still be addressed.

The hypothesis remains unresolved. This round checks a smaller representation
of the existing necessary count restrictions and tests it in two bounded runs.
The maintained range remains 191 to 235 edges, with the previously documented
independent-rebuild limitation on the contributor proof. The optimum and 196
remain open. No new mathematical definition is introduced.

## The count representation

Under a six-count total at most 22, the checked necessary intervals are

$$
([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]).
$$

For (n) corner positions and (1\le k\le n+1), at least (k) positions are
absent if and only if every set of (k-1) omitted positions leaves an absent
position outside it. If at least (k) are absent, they cannot all fit into
the omitted set. Conversely, if fewer than (k) are absent, extend their set
to (k-1) positions; the corresponding condition fails.

Lean checks this equivalence, its complementary upper bound on selected
positions, a Boolean specialization allowing repeated corner values, and the
number of clauses. At each of the six centres there are 21 corner positions.
The direct representation therefore uses

$$
4\binom{21}{0}+\binom{21}{1}+\binom{21}{2}=235
$$

clauses, with 4494 literal occurrences and no new variables. These clauses
express the same individual lower-count conditions. They leave the summed
counter's 126 corner occurrences unchanged, including repetitions over
100 distinct vertices.

## Derivation from the original input

The original bounded input contains 106348 clauses on 7277 variables.
Each of the 235 direct clauses has a reverse-unit-propagation derivation
from those original clauses alone. An independent implementation reconstructs
the original input exactly, enumerates the complete direct-clause family,
and checks all 132921 ordered references. These comprise 132686 unit
propagations followed by 235 contradictions under the respective negated
clauses. No added clause is treated as an unexplained assumption.

One encoding appends all 235 clauses, giving 106583 inputs. The other replaces
the six individual lower-bound counter families. It removes 4917 counter
clauses and leaves 2457 auxiliary variables unused, yielding 101666 clauses
with 4820 variables occurring. Original variable identifiers are retained.

Every input in the reduced formula is an original clause or a proved added
clause. Thus a contradiction can be transported back to the original input.
For a native derived identifier (x), the corresponding identifier is

$$
106583+(x-101666)=x+4917.
$$

Native input references use the saved input map. The 235 original-input
derivations must be prepended. For positive-hint RUP traces with fresh
identifiers, deletion records may be omitted because retaining additional
true clauses preserves these derivations. This argument does not extend
automatically to arbitrary RAT proofs.

The first 1000 native deductions of each saved trace were replayed against
the original input with the appropriate mapping. This is a bounded check
of proof transport. Neither entire trace nor a final contradiction is verified.

## Search outcomes and verification scope

| Input | Clauses | Variables occurring | Outcome | Wall time |
| --- | ---: | ---: | --- | ---: |
| Original plus direct clauses | 106583 | 7277 | Timeout | 180.062 s |
| Lower counters replaced | 101666 | 4820 | Timeout | 180.047 s |

Neither run returned a complete model or contradiction. The second run used
20.90625 seconds of measured process CPU time during its wall-time allowance.
Other proof jobs were active, so these runs provide no reliable speed comparison.
The partial traces remain available locally and as verified lossless gzip
archives; preservation does not make them complete proofs.

The generic counting module passed Lean in 6.890 seconds with five dependency
reports. Four use only the standard dependencies `propext`, `Classical.choice`
and `Quot.sound`; the numerical clause-count statement uses none. The initial
resource-gated attempt launched no compiler. The successful attempt and all
source, object, log and dependency hashes are preserved. The concrete
235-clause replay was checked independently in Python, not newly in Lean.

## Next mathematical restriction

The prefix 012032 already has the proved inequality

$$
\alpha_{r+2}+\alpha_{r+4}\ge8.
$$

The present reduced input exposes individual lower bounds but has no dedicated
counter for this joint inequality. The pair has 42 corner occurrences over
37 distinct vertices. Its absent count at least eight is equivalent to a
selected-occurrence count at most 34. Repeated corners must retain their
multiplicities.

The next task is to encode that existing theorem directly, then check the
new counter interpretation using the actual pair theorem and the canonical
prefix. It must not be described as a derived clause of the original input
unless a separate derivation is supplied. Any contradiction still requires
complete replay and transfer to arbitrary snakes. The proposed input is pinned
in `data/next-pair-task.json`; it has not been encoded or searched.
