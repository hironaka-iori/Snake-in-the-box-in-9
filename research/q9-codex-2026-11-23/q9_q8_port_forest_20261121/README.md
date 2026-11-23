# Q8 forest pairs in Q9

Each Q9 coordinate cut gives two labelled Q8 vertex sets. A candidate must be a linear forest and have at most two isolated vertices. An isolated vertex must use its crossing edge and becomes an endpoint. A vertex of layer degree two cannot cross. All vertices of layer degree one must cross except those designated as global endpoints. Enumerating exactly two endpoints across both layers therefore specifies both crossing-port sets. The relative Q8 isometry must match the port sets exactly. Any overlap elsewhere introduces a forbidden edge. A final walk from one endpoint checks connectivity. All nonempty pairs with at least 193 vertices in total are eligible.

The source inputs are the 131 genuine 191-edge paths in the record file and all 5,062 near-walks in the three-axis file. Every coordinate cut and both sides were used. The program chooses canonical forest representatives by aligning the longest components in both orientations, including every assignment of unused axes. The distance hash only locates candidates. The solver checks each port image explicitly and tests every remaining coordinate permutation consistent with the chosen pivot and port column counts. Both endpoint assignments across the two layers are covered, as are same-shape pairs.

| Original or edited layer pool | Distinct shapes | Partner pool | Verified port isometries | Exact whole-layer overlaps |
|---|---:|---|---:|---:|
| Record only | 1,138 | Record only | 4,555,106 | 0 |
| Record and near-walks combined | 8,738 | Same pool | 47,962,653 | 0 |
| Delete one vertex from every 106–107 vertex forest | 11,410 | All 8,738 original shapes | 64,061 | 0 |
| Delete any two vertices from every 107 vertex forest | 38,746 | All 8,738 original shapes | 10,025 | 0 |
| Repair an originally invalid layer having at least 103 vertices by one deletion | 3,386 | All 8,738 original shapes | 70,023 | 0 |

The 191-edge positive control is in `control191.log`. The independent audit in `audit.json` checks every source walk and counts all usable labelled layers, tests the indicated random provenance samples and compares the indexed algorithm with an independent full Q8 isometry search on 13 pairs. Exact whole-layer overlap means the actual overlap equals precisely the proposed crossing ports. Counts of isometries are across endpoint assignments. The result covers these input forests and edits.

To reproduce, compile the corresponding C++ sources with C++20 and optimization. Run `extract.cpp` with source labels 0 and 1 on the record and near-walk words respectively. Run `match.cpp` with target 192, exact-size flag 0 and the two layer files. For the positive control use target 191, flag 1 and just the record layer file. The editor arguments are deletions, minimum layer size, maximum layer size, maximum source count and the source layer files. Use (1,106,107,10000) or (2,107,107,7). Run `salvage.cpp` with minimum size 103 on the near-walk source. Run `cross.cpp` with the two original layer files and one edited file.
