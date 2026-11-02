# Milestone 87: retention covers and saved-edge indexing

This milestone advances the structural graph-to-snake proof. The maintained
project interval remains 191 through 235 edges; 234 remains conditional.
The existing paper stays at revision 86, with the next full revision at 96.

The new definition is a **retention cover**: a recorded graph contains every
bounded candidate key accepted by the numeric retention predicate. This
one-sided inclusion is enough to obtain saved edge indices. Exact generator
equality is a stronger sufficient condition. Additional rows still need the
weight and potential inequalities used by the upper-bound proof.

## Checked interfaces

Twenty-seven new Lean theorem audits passed across four modules. The final
source, object and log hashes and theorem-audit counts are in
[the proof summary](data/proof-summary.json).

| Module | Content | Explicit remaining premises |
| --- | --- | --- |
| RetainedEnumeration | Ordered generator membership, retention covers, inclusion, indexing, full-key uniqueness and endpoint mapping | Generic finite-data hypotheses |
| RetainedPredicates | All four actual-snake retention families, coding ranges, history compatibility and endpoints | Two reference-catalogue refutation premises |
| NumericRetention | Executable bounded tests and their truth on each fitting actual snake step | The same two reference premises |
| ArrayAssembly | A saved edge for every actual step and an in-bounds index function for the entire state walk | The two reference premises, concrete finite coverage, source-column identity and target-column identity |

The executable numeric predicate includes both source and target history
compatibility. The latter is the assertion in the original builder.
The combined imports reuse 3,101 source/object-pinned support modules. Their
namespace directories are assembled into one local search root; this changes
no inherited proof. A fresh complete dependency rebuild is not claimed.

## Exact computational evidence

- All 791 compatible direction/history blocks have exactly the independently
  reconstructed accepted code lists: 36,904,896 candidate keys and 4,947,008 rows.
- All 37,084 incompatible blocks are empty.
- Keys are strictly ordered by direction, history and count code, with no
  duplicates. Every saved source and target matches the source-derived formula.
- There are 4,740,419 distinct endpoint pairs. Exactly 206,589 endpoint pairs
  have two rows. Preserve the full key when reading an edge weight.
- The 791 blocks use only 127 different count-code sets. A shared six-way
  membership diagram has 3,981 nonterminal nodes. All roots and all block lists
  reconstruct exactly. The complete compressed representation is 29,924 bytes.

The two array audits are independent executable checks of pinned data.
They do not establish a closed Lean coverage certificate or prove equality
between the Python and Lean executable predicates. The membership diagram
is exact computational data for the next certificate, with that proof still
open. No upper-bound improvement follows from these checks alone.

Read the [mathematical note](mathematical-note.md) and the detailed
[source and array audit](audit/array-order.md). The
[checkpoint](data/checkpoint.json) preserves a later observation of the
existing case7302 replay. Its final theorem remains pending; do not restart
the live driver because a tool poll returns no output.

## Reproduction

Use the recorded Lean4.19.0 and pinned inherited environment. In order:

1. Run `scripts/check_order.py` for the source-array hashes, ordering,
   full-key ranks, endpoints and parallel-edge counts.
2. Run `scripts/check_arrays.py` for the independent retained-code comparison.
3. Run `scripts/profile_coverage.py` for the shared membership representation.
4. Run `scripts/check_enumeration.py` for the generic indexing theorems.
5. Run `scripts/check_predicates.py`, then `scripts/check_numeric.py`, then
   `scripts/check_assembly.py` for the actual-snake interfaces.

Existing successful checks need not be repeated without a changed dependency
or an independent rebuild requirement. The final scripts `finalize.py`,
`update_handoff.py` and `verify_saved.py` maintain the checkpoint and current
handover; they do not supply missing mathematical premises. The handover update
is intended once at this milestone and deliberately rejects duplicate entries.

## Next proof obligation

Prove that numeric acceptance implies acceptance by the assigned membership
diagram root, then certify the concrete row index and endpoint columns.
One possible organization covers every omitted count region by an established
exclusion. Reuse the checked universal indexing theorem after supplying these
finite premises. Keep the reference-catalogue premises explicit until their
closed dependencies are imported or rebuilt.

Edge-weight interpretation, all compatible eleven-direction credit
realizations, the five pending target shares and full potential replay remain
separate. The 235 upper bound still relies on the inspected contributor theorem
and saved audit, without a new complete independent rebuild in this round.
