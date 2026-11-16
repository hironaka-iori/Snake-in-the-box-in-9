# Parity-lift construction audit

**No blocking defect found.** Independently reconstructed all 6,763 saved graphs, their static outcomes, all 36 exported circuit models, and all 28 successful witnesses. No optimizer, compiler, or software test was run.

## Exact reduction and coverage

The parity lift maps a retained parent word x to (x, parity(x)), which has even total parity. The opposite-colour vertex over a word y is adjacent to that lift exactly when x equals y or differs from y in one coordinate. The audit derived this by direct Hamming adjacency in the larger cube and checked its agreement with every closed neighbourhood used by the producer.

A physical opposite-colour vertex with exactly two selected neighbours labels their contraction edge. Parallel labels may be collapsed for Hamiltonian-path existence: different edges of an injective ordering cannot reuse a label, since its selected neighbour pair is fixed. A Hamiltonian ordering lifts to an induced path with 2(|S|-1) edges. All endpoints and ordering are free within this exact selected parity-class family.

The 0-, 1-, and 2-omission combinations were independently enumerated in the recorded order. All parent vertex sequences and transitions were checked. IDs are exactly 0 through 6762, with no missing or repeated row and no early stop.

| Parent dimension | Rows | Isolated | Excess leaves | Disconnected | Native infeasible | Witnesses |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 106 | 41 | 27 | 2 | 8 | 28 |
| 6 | 379 | 379 | 0 | 0 | 0 | 0 |
| 7 | 1327 | 1327 | 0 | 0 | 0 | 0 |
| 8 | 4951 | 4951 | 0 | 0 | 0 | 0 |

Every graph edge count, leaf list, isolated-vertex certificate, and disconnected component matched the reconstruction. All 36 models contain exactly the expected Boolean arcs and one circuit constraint: both directions of each simple graph edge and both directions between every graph vertex and a mandatory dummy, with no self-loops. Every node therefore lies on the single circuit; removing the dummy gives precisely a Hamiltonian path. Model hashes all match the saved records.

All 28 witnesses were reconstructed from their contracted order and labels, checked for distinct vertices and correct dimension/length, and checked on every unordered vertex pair. They occur only in Q6. The eight remaining circuit results are native infeasibility reports; their contradictions were not independently replayed. No Q9 witness was produced.

## Isolation covering argument

Let I be the initially isolated parent vertices. If a retained x in I acquires a contraction edge after deleting a set D, some deleted vertex d must have shared a relevant closed neighbourhood with x. Hence their parent-cube Hamming distance is at most two. If x itself is deleted, it is also covered by this condition. Therefore removing all inherited isolation requires I to be covered by the radius-two neighbourhoods of the deleted parent vertices.

This necessity was additionally checked against every enumerated deletion: each initially isolated vertex outside that union remains in the reconstructed isolated set. If one deletion covers at most c members of I, at least ceil(|I|/c) deletions are necessary. Three initially isolated vertices whose permissible-deletion neighbourhoods are pairwise disjoint also require at least three deletions.

| Parent dimension | Initial isolated vertices | Maximum coverage by one deletion | Necessary deletions from count | Disjoint triple |
|---:|---:|---:|---:|---|
| 5 | 0 | 0 | 0 | None |
| 6 | 10 | 6 | 2 | None |
| 7 | 37 | 12 | 4 | [3, 56, 85] |
| 8 | 69 | 17 | 5 | [7, 40, 91] |

For the Q8 parent, 69 initially isolated vertices and maximum coverage 17 prove that at least five deletions are needed to remove inherited isolation. Thus every deletion of at most four parent vertices still leaves an isolated vertex; the stronger conclusion is a consequence of this small covering certificate, rather than an additional Hamiltonian search. For the Q7 parent, 37 and 12 similarly require at least four deletions. The full parent-restricted neighbourhood lists, coverage maxima, and triple witnesses are saved in the audit JSON.

The Q6 single-deletion counting bound alone requires only two deletions and supplies no disjoint triple. The additional exact pair-union calculation saved in the same audit JSON is stronger: any two deletions cover at most nine of the ten initial isolated vertices. Hence at least three deletions are necessary for the Q6 parent. This pair maximum was computed over all pairs of its 27 parent vertices; no Hamiltonian search is needed for the deduction. The resulting necessary deletion bounds for the Q6, Q7 and Q8 parents are respectively three, four and five. Their complete 0/1/2-omission exclusions also agree with the directly reconstructed isolated-vertex certificates. The Q5 parent has no initially isolated vertex, so this inherited-isolation argument gives no bound there. None of these necessary deletion bounds guarantees a path after that many deletions.

For the saved 99-vertex Q8 parent this also gives a ceiling for every successful construction obtained solely by deleting parent vertices and applying the same majority parity lift. With at least two retained vertices, Hamiltonicity requires the absence of isolated vertices and therefore at least five deletions. Its lifted edge length is consequently at most \(2(99-5-1)=186\). A singleton retained set gives length zero. This deduction covers arbitrary deletion subsets of this particular parent; it is not an additional exhaustive search, an attainment claim, or a global Q9 bound.

## Execution integrity and limits

The resource receipt is ACCEPTED_NATIVE_RESULT with exit code zero and no stop reason. All source/input/result/stdout/stderr pins match; stderr is empty and stdout agrees with the result. The resource sample arrays contain no recorded errors or Lean processes. Exact timing and sampled-memory values are retained in the audit JSON; sampled maxima are not continuous peak guarantees.

The covered families use only the four saved parent paths, their specified parity lift, and the listed omissions. They do not cover arbitrary parent snakes or arbitrary parity-class changes. The general reduction and isolation argument are written mathematical deductions; no end-to-end Lean extraction or solver-certificate claim is made.

## Pinned evidence

| File | SHA-256 |
|---|---|
| `E:\Snake-in-a-box\milestones\188-dimensional-constructions\data\lower-dimensional-seeds.json` | `d62c92cc97eae196b21aeefe2111adfb03cc3121b9b62ba7e3e2c6ee6920c20d` |
| `E:\Snake-in-a-box\milestones\233-parity-lift-construction\scripts\lift_search.py` | `dee82192e0938dbb2cff8f7d0f83edf51d8995357c21f6594482bc4fbb6bbcd4` |
| `E:\Snake-in-a-box\milestones\233-parity-lift-construction\scripts\run_lift.py` | `bb416eee59d0a5558857ee0e6215bdcf7e4693767a1d3946689d7e80431acf5b` |
| `E:\Snake-in-a-box\milestones\233-parity-lift-construction\scripts\native_resources.py` | `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413` |
| `E:\Snake-in-a-box\milestones\233-parity-lift-construction\data\lift.json` | `1fba9635cb633b509c3800622fbbdbb0796e79993a774f5e35afe9a6bb50ee98` |
| `E:\Snake-in-a-box\milestones\233-parity-lift-construction\data\lift-execution.json` | `34b44bfdada8d2e90635c7ce6592eeda427ff2efc801c24355baf0d342977980` |
| `scripts/audit_lift.py` | `a603f6acfbcf20db2b2582217571543a0f9ae772a49647acd72adc5aa67304ed` |
| `data/lift-audit.json` | `9de9810cafdc2f6dca878684a7c67d1c687ef0b0bf80dc349adb3f68bd962b43` |

Only the assigned audit script, audit JSON, and this report were written. Existing search evidence and documents were unchanged.
