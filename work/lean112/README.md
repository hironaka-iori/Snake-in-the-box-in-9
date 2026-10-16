# First complete KEEP=112 entry

The target is the **forward orientation of bank entry 0**, with its first 112
vertices fixed. This is one of 262 oriented entries. It is a conditional
extension exclusion, not a global upper bound for the nine-dimensional cube.

The final declarations in `First112Complete.lean` are:

- `Snake9.Regrowth.First112.no192`: a 192-edge snake cannot start with this
  fixed 112-vertex segment.
- `Snake9.Regrowth.First112.no_long_prefix`: the same holds for every length
  at least 192 edges, by taking an initial 192-edge segment.
- `Snake9.Regrowth.First112.no_long_suffix`: the corresponding statement
  obtained by reversing the snake.

These declarations count as completed only when the full build and the
completion audit below pass. The authoritative receipt is
`outputs/lean112/first-geometric-proof.json`.

## Proof construction

1. A hypothetical 192-edge snake leaves an induced 81-edge suffix starting at
   index 111. This suffix has 82 distinct vertices.
2. `First112Data.lean` verifies the fixed banned-neighborhood mask and a
   closed reachable region by kernel reduction. `suffix_covered` proves
   that every suffix vertex is in that region, using the existing `ValidExt`
   soundness lemmas. The region has 122 vertices.
3. `RegrowthBridge.lean` proves the path constraints: every selected vertex
   has a selected neighbor, its degree is at most two, endpoints have degree
   at most one, and an induced path contains no four-cycle. It also proves
   that exactly 41 suffix vertices have odd bit parity, and that there is
   at most one endpoint besides the fixed head.
4. `First112Semantics.lean` assigns an explicit meaning to each Boolean
   variable. Selection and endpoint variables denote path properties.
   Every auxiliary totalizer wire denotes an integer count threshold; its
   meaning is independent of the solver.
5. The 49 `First112Clauses*.lean` modules prove all **1,547 clauses actually
   used by the previously checked Boolean certificate**. Counter clauses
   follow from list-count addition. The retained bounds say that at most
   22 of the 63 odd vertices are absent, and at most one other endpoint is
   present.
6. `all_constraints` constructs the precise imported `Constraints` record.
   The existing `constraints_unsat` theorem then yields a contradiction.

The Python generator is untrusted. Lean checks the emitted finite facts and
every generated proof, including exact field types in the imported Boolean
certificate. The final audit checks the three theorem declarations for the
standard axioms `propext`, `Classical.choice`, and `Quot.sound` only.

## Reproduction

Use Lean 4.19.0 and the existing compiled dependency and Boolean-certificate
artifacts. The local helper locates the same Lean distribution used for the
completed KEEP=144 build.

From the repository root, using Python 3.12 or later:

```text
python work/lean112/generate_bridge.py
python work/lean112/check.py PathStructure BallClauseLogic
python work/lean112/run_first_bridge.py
python work/lean112/verify_first.py
```

The build saves logs and source/artifact hash receipts after every module.
Resumption accepts a cached module only when both hashes match. The final
module is always checked again. `verify_first.py` additionally verifies all
150 Boolean-certificate receipts, the bank-prefix identity, and the final
axiom audit before recording a completed geometric entry.

The live dashboard's completed-entry count is updated by that audit, not by
the solver survey or by the number of intermediate modules.
