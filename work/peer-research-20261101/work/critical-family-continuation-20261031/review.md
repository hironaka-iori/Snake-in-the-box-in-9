# Independent small-SCC continuation review — 2026-10-31

New rigorous result at the direction-word level: each of the three small directed cycles in the downloaded OLD six-component critical family admits no internally induced Q9 realization of nine consecutive graph edges. All ten starting phases were checked, with complete branching over forgotten/new coordinate labels. This supplies ten new valid length-nine forbidden histories for that frozen indexing. It does not establish a new mean or global snake bound, or coverage of the current eight-case graph.

## Source and closed cycles

The 6,380,307-byte `critical_edges_frozen.json` has 18,865 records and SHA256 `2a19ca61f96985b5063d8ef20534a9c5e6fe7ac9c0d21e4de451a1d4bddebc5f`, matching the supplied frozen digest. Its component groups are:

| Component | Nodes | Edges | Reviewed here |
|---|---:|---:|---|
| 264110 | 106 | 168 | Not analyzed |
| 286269 | 4 | 4 | All four phases |
| 262705 | 2 | 2 | Both phases |
| 283106 | 4 | 4 | All four phases |
| 173807 | 3,398 | 10,543 | Not analyzed |
| 223850 | 2,611 | 8,144 | Not analyzed |

Within each small group there is exactly one outgoing edge per node and following endpoints traverses one closed directed cycle covering all its nodes. Cycle orders (with cyclic shifts allowed) are:

- 286269: [147366,2230713,149903,2230218].
- 262705: [147549,2231553].
- 283106: [148337,2229493,148854,2231721].

Each has mean recorded weight 480. These are the OLD frozen records, not a certificate that they remain critical in, or fully characterize, a later graph. The parent is handling the old six-case versus current eight-case audit/filter separately.

## Correct lifting with new labels

A graph edge specifies a canonical nine-direction window. Two consecutive windows overlap in eight directions. Given a literal realization of the old window, the next canonical word's first eight entries define a partial injective map from its labels to actual cube coordinates. If two occurrences of one label disagree, or distinct labels would map to the same coordinate, the edge sequence is inconsistent. If the appended label is already in that map, its literal coordinate is fixed. Otherwise every coordinate in {0,...,8} outside the partial map's image must be considered. Such a coordinate may have occurred earlier outside the current overlap. It must not automatically be fixed to the old periodic coordinate or required to be globally unused.

Counterexample to the shortcut: the canonical three-direction window [0,1,2] may repeat while literal directions are [0,1,2,3,4,5], a monotone induced Q9 path. Replacing them by a literal period-three repetition [0,1,2,0,1] invents a chord at step five. A periodic sequence of canonical words therefore need not have a fixed literal period. The earlier unique-lift seven-edge cycle did have all labels present in every overlap; these new cycles do not.

## Finite complete geometric proof

For each phase fix the initial nine-direction word to its canonical coordinates 0..5, starting at cube vertex zero. This loses no case: any actual initial position can be translated to zero, and any injective embedding of its six direction labels can be carried to these coordinates by a cube coordinate permutation. Subsequent coordinates are then branched over the complete nine-coordinate set.

At each extension, append the allowed coordinate and reject it precisely when its new cube vertex equals or is adjacent to any previous vertex other than the immediate predecessor. A valid continuation must pass this test. No branches are merged or quotient-pruned. By induction every possible internally induced realization of the edge-history remains in the frontier. If the frontier is empty, that entire finite edge-history is impossible for every genuine snake.

`analyze_small_cycles.py` performs the partial-map branching and records every frontier's sorted direction-word SHA256. All ten phases have nonempty frontiers through graph edge eight (six survivors each) and empty frontier at graph edge nine. For phases beginning with window A below, frontier sizes at edges 1..9 are

    1,1,3,3,6,6,6,6,0.

For phases beginning with window B they are

    1,4,3,9,6,12,6,6,0.

Thus each phase has only 32 or 47 cumulative live prefixes. Edge nine represents seventeen literal transitions, since the first graph edge provides nine directions and each subsequent edge adds one. Some branches already produce chords at eleven or thirteen transitions; the universal extinction threshold is seventeen. This is an exhaustive finite dimensional obstruction, not an assumption of literal periodicity.

Two sixteen-transition survivors, before the final unavoidable obstruction, are:

- A: [0,1,2,0,3,2,4,3,5,4,6,5,7,6,8,7].
- B: [0,1,2,3,1,4,3,5,4,6,5,7,6,8,7,0].

These are genuine internally induced cube paths. They establish that eight graph edges cannot be excluded by these direction-window and internal chord constraints alone. They do NOT prove that the recorded count/history metadata is jointly realizable by a global snake; other inequalities might eliminate a shorter full model pattern.

The independent checker `independent_check.py` does not import the branch-lifting implementation. Instead it tries ALL nine coordinates at every live prefix, canonicalizes the entire final nine-direction word, and checks inducedness of the complete path using symmetric differences of sets of coordinate flips. It compares the complete frontier hashes, not just their sizes. Its 3,555 coordinate trials reproduce all ten empty frontiers and all prior frontier hashes. `independent_check.json` reports PASS. This is an executable exhaustive proof at this finite scale; no Lean compilation was performed.

## Registering the new rules safely

`review.json` includes the exact nine edge IDs for every forbidden phase under `forbidden_9edge_pattern`. Keep order and multiplicity. No individual edge, single tour, or entire SCC can be deleted from the original graph on this basis. For these three simple directed marked subgraphs, a finite-history lift can track runs of their own cycle-edge membership and forbid the ninth consecutive member, resetting on every edge outside that cycle. This is valid because within each marked subgraph consecutive edges necessarily follow the one cycle. A combined lift must not confuse these sets with another graph's renumbered edges.

Recomputing the resulting global minimum mean requires the remaining critical family and a complete automaton/potential calculation. The two large components and the 106-node component remain untouched here. Even eliminating all three small repeated cycles does not show that mean480 rises, and any new potential range must enter the global bound calculation. The arbitrary-snake interpretation of the source finite model remains a separate obligation. Nothing in this review claims coverage of the current eight-case graph or a new global numerical upper bound.

All new files are under this review directory. No old script, manifest or source graph was modified, and no upload was performed.

## Follow-up: current-case filtering and larger-cycle probes

`review_filter_and_probes.py` independently reconstructs the filtering by explicit vertex-position count lookup and whole-bucket interval membership. It checks bucket6 against every integer 6..21, rather than pretending the actual count equals6. For the applied completed cases, no interval partially intersects that bucket. Directions are canonicalized after optional reversal, and the four internal vertex-count positions are reversed consistently. Results exactly match the stored complete retained record list:

- case7203 hits116 records, case7216 hits34, intersection22;
- 128 distinct deletions, 18,737 retained records;
- all ten edges of the three reviewed small cycles remain present.

This follows the listed applied cases, not all cases whose standalone probe_status says UNSAT. It filters the frozen critical subset; it does not re-extract the complete critical family of the current eight-case model. Original component labels may split after filtering and require fresh SCC computation.

The larger `probe_critical_cycles.py` collects specific cycles and tests one selected phase per cyclic-rotation deduplication class. Its fresh-coordinate compression is sound: after translating the initial vertex to zero, every globally unused coordinate is zero in all previous vertices. Permutations of those unused coordinates fix the complete past, so all possible next globally unused coordinates are equivalent and the least one is a representative. Historically used coordinates absent from the overlap are not equivalent under this stabilizer and correctly remain separate choices.

Its per-level dedup key (literal tail8, current cube vertex, set of seen cube vertices, set of used coordinates) determines every future window-overlap constraint, chord/repetition test, and used-versus-unused coordinate choice. Earlier chronological order is irrelevant once these data agree. The next abstract word is fixed by the selected cycle and the current level; merging states across unrelated levels/cycles without that context would require a larger key. Thus the local dedup is safe.

More strongly, this review did not rely on either optimization to accept the 107 refutations. An independent direct oracle rechecked every specifically REFUTED history by trying all nine coordinate choices, canonicalizing the full last nine-direction window, and checking the literal path geometry, without fresh-coordinate symmetry and without state deduplication. All 107 frontiers become empty by their stated forbidden length. Across these proofs there were42,228 coordinate trials and the largest uncompressed frontier had204 prefixes. Full source edge closure was checked for every sampled cycle. These results are in `filter_and_probe_review.json`, with source hashes and explicit checked histories.

Two STATE_LIMIT and one DEPTH_LIMIT cases are unresolved, not refutations. A single selected-phase history does not authorize a uniform membership-run cap for all cyclic phases, nor deletion of an entire cycle/SCC. To enforce precisely those histories, an Aho-Corasick or other explicit suffix-history automaton is appropriate. Every nonempty edge-ID prefix has one determined endpoint (its last edge's target), so only that original graph vertex needs the corresponding extra state; this can avoid a full graph-times-language product. Every transition still must check source/target consistency, retain all unmarked outgoing alternatives, reject terminal matches including failure-link suffix matches, and preserve weights. This paragraph reviews the proposed construction's mathematics, not an implementation that has not yet been supplied.

No complete current-graph mean or global upper bound follows from these107 checked finite histories alone.

Final follow-up: all222 histories, full compact lift and exact surviving mean480 were independently checked; see `review_final_lift.md`, `review_final_lift.py` and `final_independent_review.json`. This supersedes the earlier107-pattern review scope without claiming a full-current-graph reconstruction.
