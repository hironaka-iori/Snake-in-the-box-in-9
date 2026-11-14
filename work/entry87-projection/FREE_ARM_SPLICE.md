# Regrowing a bridge between two independently placed source arms

Fix a 191-edge source. Remove k internal vertices. Keep both outside arms isometric to their original ordered paths, with independent orientations and translations. Connect the two hinge vertices by k+2 edges to obtain the desired 192-edge total. This family allows rotations of one complete arm in addition to [unrestricted translations](TRANSLATED_SPLICES.md).

**Theorem.** In this family, every one of the 131 bank snakes requires removal of at least 45 original internal vertices to obtain 192 edges. Both outside arms are required to be nonempty.

To prove this, first place one arm exactly as in the source, using a common isometry of the completed cube. Reversing the full path is allowed, so the longer arm can be the fixed one. Enumerate all possible starting addresses of the shorter arm. It must avoid the closed neighbourhood of the fixed arm, have the correct parity, and be within k+2 of its hinge. Now build the shorter arm in its stored transition order. At the first appearance of a coordinate, assign it any target direction not previously used. At previously named coordinates, the image transition is forced. A partial image can be discarded as soon as it meets the fixed arm or any of its neighbours. Every injective assignment of the appearing directions extends to a cube coordinate permutation. This argument includes all relative isometries and avoids repeating unused permutations.

For each pair of arms that has no cross-contact, exhaust every bridge with the [induced-splice recursion](translated_splice.cpp). Small and large arm placements are not required to agree even at the original hinge coordinates. Testing only k=44 covers all smaller values: extend the removed interval outward, keeping a vertex on each side, and use the same two isometries and the very same completed path.

At k=44 there are 1,133,705 choices of source, split and free hinge address passing the initial filters. The orientation recursion visits 1,278,751,217 partial states. Exactly 667,538 complete relative placements survive. Their bridge searches visit 14,754,326,554 partial paths, with zero witnesses. Positive controls reconstruct an induced path after deliberately deleting an interior transition. Restricting all axes to the identity separately reproduces the translation-only placement totals from an independent implementation.

[Native enumerator](arc_placements.cpp), [source and independent checks](arc_placements.py), [per-source totals](arc-placements-44-0-131-0-192.json).
