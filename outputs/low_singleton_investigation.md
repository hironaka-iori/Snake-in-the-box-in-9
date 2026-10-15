# One-singleton local configurations

Checkpoint: 15 October 2026. The checked interval remains 191 <= a(9) <= 254; the conjecture 196 remains unresolved.

## Checked necessary condition

`work/spectral/LowSingletonArms.lean` proves a structural restriction under explicit geometric premises. Translate the selected root to zero, with selected unit neighbors in directions a and b. Outside these directions, suppose all pair vertices except possibly the pair {u,v} are selected and all selected pair vertices are internal in the path. If the second selected neighbors of the two unit vertices have directions i and j, then (i,j) must equal (u,v) or (v,u).

The argument first excludes a continuation coordinate outside the exceptional pair: two ordinary pair vertices then force two additional neighbors at a vertex that already has a selected neighbor. It next excludes both continuations using the same exceptional coordinate: three pair vertices need support from two vertices whose remaining degree capacity is only two in total. The implementation proves these steps and their combination. Axiom audits contain only propext, Classical.choice, and Quot.sound.

In the proposed application, exactly one singleton square supplies the exceptional pair, and endpoints at Hamming distance at least three imply that the selected pair vertices are internal. The formalized theorem is stated through the explicit coordinate, membership, and internal-vertex premises above. It is not a proof of the full assertion that every one-singleton vertex lies within distance two of an endpoint.

## Checked obstruction to a purely local proof

`work/low_singleton_radius3.py` searches a radius-three relaxation in the remaining split configuration: root directions 0 and 1, exceptional pair 2 and 3, and selected second neighbors 5 and 10. It forces degree two at selected vertices of weight at most two and forbids degree above two; cycle cuts exclude cyclic components.

The result is a 60-vertex induced linear forest with 14 components, all vertices of weight at most three, degree two at every selected vertex of weight at most two, and exactly one singleton square at zero. `work/final_lean/RadiusThreeForest.lean` independently checks the explicit component paths, pairwise disjointness and absence of intercomponent edges, radius bounds, degree counts, and the singleton-square enumeration. The finite certificates depend only on propext. The paper prints all 14 paths.

This is not one connected Q9 snake. It demonstrates that the radius-three degree and acyclicity conditions by themselves do not rule out the remaining configuration. Any proof of endpoint proximity needs global connectivity or further constraints involving higher-weight vertices. The previously recorded full-path solver exclusion with endpoints at distance at least three remains uncertified.

## Reproduction

The core now contains 16 modules. Run `lake build` in `work/final_lean` to check the finite forest and the prior core results. The general arm restriction uses the pinned mathlib dependency described in `work/spectral/README.md`:

```sh
python work/spectral/verify_incidence.py --module LowSingletonArms --mathlib-dir /path/to/mathlib
```

The default module remains SquareIncidence and still checks the bound 254. Logs for this round are `outputs/low-singleton-core-build.log` and `outputs/low-singleton-arms-build.log`. The solver experiment can be repeated with the pinned OR-Tools dependency:

```sh
python work/low_singleton_radius3.py
```

The static Lean certificate is the authoritative evidence for the displayed forest; a new solver run should be compared with it before treating a different output as checked.

## Uncertified radius-four to radius-six experiments

The additional program `work/low_singleton_ball.py` fixes the same normalized radius-two selection. Selected vertices strictly inside the ball have degree one or two, with no endpoints at weight at most two; the total number of interior endpoints is bounded by the stated budget. Boundary vertices may have degree zero, one, or two. Global connectivity is not required. Forest runs remove cyclic components through valid cycle cuts.

| Radius | Interior endpoint budget | Cycles | Solver status | Cycle cuts |
|---|---|---|---|---|
| 4 | 2 | Allowed | OPTIMAL | 0 |
| 4 | 2 | Forbidden | OPTIMAL | 22 |
| 5 | 2 | Allowed | OPTIMAL | 0 |
| 5 | 2 | Forbidden | INFEASIBLE | 41 |
| 5 | 3 | Forbidden | INFEASIBLE | 40 |
| 5 | 4 | Forbidden | OPTIMAL | 24 |
| 6 | 2 | Forbidden | INFEASIBLE | 53 |

All seven records use one worker and seed 29; time limits, elapsed times, and per-iteration solver statistics are saved in `outputs/low_singleton_ball_*.json`. For a feasibility problem, OPTIMAL means a feasible assignment was found; it does not mean that a longest snake was found. The four saved feasible assignments were independently checked during the publication audit for the normalized selection, degrees, endpoint budget, and, where required, absence of cycles.

The radius-five model is infeasible with at most three interior endpoints and feasible with four, according to the solver. Allowing cycles makes the radius-five model feasible with budget two. This identifies a concrete candidate obstruction involving both acyclicity and endpoint count. These exclusions have no Lean-checked certificate. The saved records contain cycle-cut counts, not the actual cycle clauses, so they do not by themselves reconstruct an impossibility proof.

The most focused next proof task is to certify the radius-five, budget-two exclusion and prove that the normalized restriction of an actual snake satisfies the encoded constraints. The earlier arm theorem still requires its explicit geometric premises; deriving those premises and the normalization from a general one-singleton vertex must also be checked. Only after those steps could this support an endpoint-proximity theorem. No improved global bound follows from the present records.

Reproduce a representative run with the pinned solver dependency, preserving the old output first:

```sh
python work/low_singleton_ball.py --radius 5 --endpoint-budget 2 --seconds 30
```

This publication includes existing experimental work only; further proof and search work is deferred.

## Certificate follow-up

The budget-two radius-five run was repeated while preserving all 41 cycle cuts. A separate Boolean encoding and proof translation now certify a 567-clause contradiction in Lean. The recorded cycle cuts and generic degree/endpoint clause implications are also checked. The complete geometric interpretation of the input clauses remains unfinished. See `ball_certificate_investigation.md` for the current evidence boundary and reproduction steps. The older solver records above remain unchanged.
