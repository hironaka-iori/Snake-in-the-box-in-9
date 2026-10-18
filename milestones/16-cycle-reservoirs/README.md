# Larger cycle configurations and local cell states

Checkpoint: 18 October 2026. Target: a 196-edge snake. New intermediate
configurations are disconnected and do not improve the 191-edge lower bound.

## A 224-vertex product

The search found two disjoint induced 14-cycles in Q5, in cyclic order:

```
A: 0,1,17,25,27,31,15,13,12,28,20,22,18,2
B: 3,11,9,8,24,26,30,14,6,4,5,21,23,19
```

Lean checked both cyclic adjacency equivalences, distinctness, lengths, and
disjointness. Placing A or B in the sixteen Q5 cells of Q4 x Q5 according to
outer parity gives sixteen nonadjacent 14-cycles, totaling 224 vertices. The
checked disjoint-color lemma explains why equal projected vertices cannot
create cross-cell edges. The concrete product was independently checked.
No novelty claim is made for this product principle.

The initial base probes were:

| Base dimension | Vertices per base set | Result | Components in each set | Q9 product vertices |
|---|---:|---|---|---:|
| 5 | 14 | Feasible | One 14-cycle | 224 |
| 6 | 26 | Feasible control | One 26-cycle | 208 |
| 6 | 28 | Feasible | Two 14-cycles | 224 |
| 7 | 54 | UNKNOWN after 60 seconds | Unresolved | 216 if feasible |

All probes exclude four-cycles. The Q6 size-28 result does not supply a
28-cycle: its two components must not be combined into a false coil claim.

## Why simple trimming fails, and actual replacements

Keeping whole 14-cycles and one nontrivial proper path from a single 14-cycle
would leave $14k+r$ vertices with $2\le r\le13$. This cannot equal 197, whose
remainder modulo 14 is one. Lean checked this arithmetic obstruction. It
concerns that trimming operation only, not arbitrary constructions.

Instead, release several cells and replace them jointly by one induced path,
free of edges to the cycles retained elsewhere. This produced:

| Released layers | New path length | Remaining cycles | Total vertices | Result |
|---|---:|---:|---:|---|
| 0,1,2 | 14 edges | Thirteen 14-cycles | 197 | Independently checked |
| 0,1,2,3 | 28 edges | Twelve 14-cycles | 197 | Independently checked |
| 0,1,2,4 | 28 edges | Twelve 14-cycles | 197 | Independently checked |

The first 5, 6, 7, and 8 layers gave targets of 42, 56, 70, and 84 path edges;
each remained UNKNOWN after 60 seconds. The successful short replacements do
not establish that the longer ones exist. Frozen-cycle constraints restrict
these experiments; none gives a global impossibility result.

## Four connector vertices

The common unused base vertices are $U=\{7,10,16,29\}$. In the restricted cell
family, an $A$-cell allows $A\cup U$, and a $B$-cell allows $B\cup U$. Each cell
has 18 allowed vertices. The only common projected vertices in neighboring
cells are the four vertices in U, so all cross-cell connections use them.

| Connector | Neighbors on A | Neighbors on B |
|---|---:|---:|
| 7 | 1 | 4 |
| 10 | 1 | 4 |
| 16 | 4 | 1 |
| 29 | 4 | 1 |

These counts were checked in Lean. If a selected connector has an external
selected neighbor, at most one of four internal cycle neighbors may remain
selected, because a snake has selected degree at most two. The resulting
omission of at least three neighbors is proved in `four_neighbor_connector_cost`.
Costs can overlap between connectors, so they must not be summed as independent
global losses. This local interaction motivates explicit cell states.

## Prepared local-state tables

`scripts/cell_census.py` visits all 262,144 subsets of each 18-vertex cell and
retains 4,973 states per type. A state records its selected mask, selected
connectors, internal degree at each connector, number of nonconnector endpoints,
and vertex count. Selected nonconnector vertices have degree one or two;
selected connectors may have internal degree zero, one, or two. At most two
nonconnector endpoints are allowed. Internal cycles are allowed at this stage.

The independent checkpoint audit checks every saved row by direct pairwise
adjacency. Enumeration completeness is not Lean-certified. Global constraints
still have to enforce connector degrees across adjacent cells, exactly two
total endpoints, 197 selected vertices, and eventually one connected path.
The tables are preparation for that constructive model, not a solution.

## Reproduction and evidence

From the repository root, using the established Python and OR-Tools versions:

```sh
python milestones/16-cycle-reservoirs/scripts/probe_base_pairs.py --n 5 --size 14 --output milestones/16-cycle-reservoirs/data/new-base.json
python milestones/16-cycle-reservoirs/scripts/build_dense_seed.py --layers 0,1,2,3 --output milestones/16-cycle-reservoirs/data/new-seed.json
python milestones/16-cycle-reservoirs/scripts/cell_census.py
python milestones/16-cycle-reservoirs/scripts/verify_checkpoint.py
```

The seed builder and census read the saved `base5-size14.json`, not the new
base output in this example. Preserve existing records before replacing that
input. The Lean module uses the pinned runtime and library paths from milestone
14. Check it with `lake env lean` on the absolute `lean/BasePair.lean` path.
Nine theorem audits pass with only standard axioms. The combined checkpoint
manifest also covers the two frozen-cut theorems from milestone 15.

The next step is to build the global construction model from these cell tables
and independently validate every resulting vertex set. The final target
remains a single 196-edge induced path, followed by an optimality proof handled
in coordination with the separate upper-bound investigations.
