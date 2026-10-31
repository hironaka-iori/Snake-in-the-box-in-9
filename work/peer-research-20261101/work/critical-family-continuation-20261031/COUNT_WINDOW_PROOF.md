# Forbidden four-count condition from a checked geometric CNF core

Let a,b,c,d,e be five pairwise distinct Q9 coordinate directions. Let x0,...,x9 be ten consecutive vertices of a snake with direction word

    (a,b,c,d,b,a,e,c,a).

Let alpha_i be the number of coordinate squares containing xi and no other selected vertex of the complete snake. Then the following simultaneous conditions are impossible:

    alpha_3 = 3,   alpha_4 <= 5,   alpha_5 <= 3,   alpha_7 <= 5.

No conditions are imposed on the other internal counts. This is an ordinary mathematical/computational local exclusion, with a fresh independently parsed RUP proof and source reconstruction; it is NOT claimed as a fresh Lean theorem or a new global bound. No novelty priority is asserted.

## Proof

Translate x0 to0 and permute coordinates a,b,c,d,e to0,1,2,3,4. This extends to a Q9 automorphism and preserves adjacency, inducedness and singleton-square counts. The path window becomes

    [0,1,3,7,15,13,12,28,24,25].

Take the union B of radius-four balls about the eight internal centers and variables X_v for selected vertices v in B. Assign X_v from the complete genuine snake restricted to B. The following are necessary:

1. Every window vertex is selected. No selected vertex has three selected neighbors. Every selected vertex whose whole neighborhood is in B has degree at least one, since the whole snake is nontrivial.
2. An endpoint witness e_v is true exactly at a selected degree-one vertex. This interpretation satisfies the selected/degree clauses. A single global nontrivial path has only two such vertices, so at most two interior endpoint witnesses are true. Unknown boundary neighbors are never set to zero.
3. No complete four- or six-cycle can be selected in an induced path. The independent checker verifies the three cycle clauses in the extracted core as actual connected2-regular four/six-vertex cube graphs.
4. At an internal center the two window-neighbor coordinates are already selected. Its other seven unit neighbors are absent by degree at most two. Singleton squares are therefore in bijection with absent pair corners among those seven directions:21 possible pairs. The stated upper/lower alpha bounds translate to at-most constraints on absent/selected pair corners.
5. For every at-most-k sequential-counter group on literals l1,...,ln, assign auxiliary s[i,j] true exactly when at least j+1 of the first i+1 literals are true. If at most k inputs are true, every implication and overflow clause in the encoding holds. Thus auxiliary variables always have an extension for a genuine snake satisfying the corresponding bound. Counter groups for omitted bounds are not required to satisfy an unused final constraint.

The standalone core retains1,052 original clauses on776 renamed variables. Every retained input clause is one of the necessary clauses above. The only alpha-bound clause kinds retained are:

    alpha<=3 at x3=7; alpha>=3 at x3=7;
    alpha<=5 at x4=15;
    alpha<=3 at x5=13;
    alpha<=5 at x7=28.

Consequently a genuine snake satisfying exactly the four displayed hypotheses would provide a satisfying assignment to all core clauses, with no need to assume the other recorded development counts. The manifest lists every retained original row, every renamed variable's source ID and exact source hashes. The independent verifier rebuilds the encoder and checks all1,052 row identities and this alpha-kind support.

The DIMACS/LRAT files then give353 positive-hint RUP steps,30,020 checked hints, ending in the empty clause. A RUP addition is valid because assuming the negation of its proposed clause and propagating its listed unit clauses produces a contradiction. Inductively each added clause follows from the original core; the empty clause proves the core unsatisfiable. This contradicts the satisfying assignment above and proves the exclusion. Cube isometry transports it back to arbitrary distinct a,b,c,d,e and any window position.

## Provenance and correction of the exploratory interpretation

The proof was discovered in an auxiliary weighted-empty-face search at cap15. Runs at31 and63 returned the same proof dependencies. A backward dependency audit found that every needed original clause was already among the75,003 base geometry/count clauses: no share cap, face definition or PB clause was used. The stronger result is the ordinary count-window impossibility above. Earlier stated share lower bounds16/32/64 for the original exact profile are vacuous consequences of an impossible antecedent and are not counted as independent nonvacuous share improvements.

A cold solve of the large base formula returned UNKNOWN at ten seconds; this is consistent with the existing UNSAT proof. The augmented search changed search behavior, and trimming its dependencies recovered a compact pure-base certificate. A cold timeout does not invalidate a separately checked proof.

## Global effect

Applying the four-count condition to the explicitly retained frozen critical subset removes two original records. The full5-million-edge current graph was not loaded, so its total removed-row count is unmeasured. Rebuilding the431-direction-history product on the reduced subset still yields two cyclic components and an exact mean480 witness. Thus this local exclusion by itself does not establish234. Further count or positive-share information is still required, followed by the full graph-to-snake and formal-replay obligations.

## Reproduce

    python trim_count_certificate.py
    python verify_count_window_certificate.py
    python apply_count_rule.py

The first command regenerates the standalone core from the saved auxiliary proof. The second independently reads DIMACS/LRAT, reconstructs every source row, checks support and validates cube-cycle clauses. The third applies only the proved forward rule; it does not assume an unavailable reversed count position.
