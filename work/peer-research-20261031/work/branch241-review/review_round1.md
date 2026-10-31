# Independent review, round 1

Scope: charge_fast.py, encoding/cheap_folded.py, pb_binary.py, github_query.py, solve_window.py, math_findings.md. Reviewed 2026-10-29. Original repository unchanged.

## Outcome

No mathematical counterexample or soundness bug was found in the current valid-input pipeline. This is a positive audit result, not a numerical upper-bound theorem. The existing bank witness is insufficient by itself, so new tests avoid the bank entirely.

Independent tests in independent_encoding_review.py passed:

- Every one of the 193 subsets of Q3 containing no full square; 672 selected-root rational-score comparisons.
- 56 random, arbitrary Q9 selected sets containing the rooted fixed path, with no full square. These need not be paths: the oracle checks the score on the strictly larger class asserted by the mathematics. Every folded objective equals an independent coordinate enumeration and Charges.cheap, including the occupancy bonus.
- Arbitrary selected-vertex deletions compared against complete rebuilds on those 56 sets.
- 960 exhaustive input assignments for random signed/repeated-literal positive weighted PB constraints with coefficients up to 59.

Results are recorded in independent_encoding_results.json. These tests supplement, rather than replace, the mathematical arguments.

## Proof details checked

The empty mother cube count D=3e3 is valid because a distance-one coordinate cube has a unique nearest corner and exactly three square faces through that corner. The integer support polynomial (h-r)(h-r-1) is nonnegative for every integral h; no continuous-support assumption is being smuggled in. The C2,3 term correctly vanishes. The direct global lemma's per-empty-face contribution simplifies to h(13-h)+2(h-7)n1/3+(h-7)n2/3, at most 42. The exact adaptive sum includes the undominated-face correction; discarding it only weakens the upper estimate.

The folding units follow from two selected neighbors of every internal window centre. Empty and mixed-event gates are equivalences. The binary comparator processes low bits first and lets each higher bit override the previous comparison, which gives the correct <= relation. Sequential-counter variable remapping preserves all source geometric clauses.

## Limits and concrete hardening recommendations

1. A free selected set is free only around one fixed direction shape. An UNSAT result excludes that shape and cap; a universal window threshold still requires all canonical induced direction shapes plus the project aggregation/automaton bridge.
2. A local SAT model may contain disconnected paths or isolated boundary vertices. This is an allowed necessary-condition relaxation, not a genuine snake construction. The existing LOCAL_SAT warning is appropriate.
3. Cold DRUP alone cannot justify lazy cycle cuts as initial axioms. Save the cut vertex sets, their source model, and a verifier that checks each induces a 2-regular connected cube subgraph. The project theorem that a snake contains no selected cycle then validates the cuts. Current scripts correctly do not claim certificate_checked=True.
4. The new standalone PB builder and its geometric bridge have no Lean soundness proof yet. Even an independently checked RUP proof certifies their emitted CNF; it does not by itself establish the intended mathematical implication.
5. Recommended implementation change: allow a dependency-free solver backend, retain a cut manifest, store input/source SHA256s, and independently check every SAT assignment and every UNSAT proof. These changes address actual remaining computational blockers without changing the mathematics.

No minimal mathematical counterexample is provided because none was found. The review does not invent a defect to satisfy a checklist.
