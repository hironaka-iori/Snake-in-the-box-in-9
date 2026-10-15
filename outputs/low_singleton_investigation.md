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
