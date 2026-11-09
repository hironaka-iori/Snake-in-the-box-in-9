# The layering inequality, derived with care

Let P be a snake (induced path) in Q_N with m edges and v = m + 1 vertices. For a coordinate i,
write k = k_i for the number of edges of P in direction i, and H_0, H_1 for the two halves
(each a copy of Q_{N-1}).

1. **Pieces.** Deleting the k crossing edges cuts P into k + 1 subpaths ("pieces"). Consecutive
   pieces lie in opposite halves, because each crossing edge changes coordinate i. So the half
   that holds the first piece (half a) holds floor(k/2) + 1 pieces, and the other half (half b)
   holds ceil(k/2) pieces. For k = 0 the whole snake lies in one half.
2. **Each half is an induced linear forest of Q_{N-1}.** The pieces in H_a are disjoint paths.
   Any edge of Q_{N-1} between two vertices of H_a ∩ P is an edge of Q_N between two snake
   vertices, so it is a path edge, and it is not a crossing edge. So it lies inside a piece. The
   induced subgraph is therefore exactly the disjoint union of the pieces.
3. **Short pieces.** An internal piece (neither the first nor the last) has at least 3 vertices.
   - A 1-vertex internal piece x would have both path neighbours equal to x + e_i.
   - A 2-vertex internal piece a-b would make a' = a + e_i and b' = b + e_i two snake vertices
     that are adjacent in Q_N (they differ in the direction of ab) but are not consecutive on
     P. That is a chord.

   So only the two end pieces can have fewer than 3 vertices. If k is even, both end pieces are
   in half a, and half b has no short piece. If k is odd, each half holds one end piece.
4. **Inequality.** Write g3_{N-1}(p, t) for the largest induced linear forest of Q_{N-1} with
   exactly p paths, at most t of which have fewer than 3 vertices. Then

       m + 1 = v ≤ G(k) := g3(floor(k/2)+1, t_a) + g3(ceil(k/2), t_b),
       (t_a, t_b) = (2, 0) if k is even, (1, 1) if k is odd.

   Any upper bound may replace g3, in particular g(p), the largest forest with at most p paths.
5. **Coordinate usage.** Σ_i k_i = m, so min_i k_i ≤ floor(m/N). The snake with m edges is
   excluded when G(k) ≤ m for every k ≤ floor(m/N).

   For N = 9, a(9) ≤ B needs G(k) ≤ m for all k ≤ floor(m/9) and all m in (B, 235]. G is
   monotone, so the binding case is m = B + 1:
   - B = 234: G(26) = g3_8(14,2) + g3_8(13,0) ≤ 235.
   - B = 233: the same pair, now required to be ≤ 234.
   - B = 226: G(25) = g3_8(13,1) + g3_8(13,1) ≤ 227.
6. **Parity.** k_i ≡ (u_i + w_i) mod 2 for the end vertices u, w of P. This decides which of the
   two (t_a, t_b) cases occurs, but it does not restrict the minimum. The number of odd k_i is
   the distance d(u, w), which is ≡ m (mod 2). None of these facts improves the bound beyond
   step 5.
7. **Edge-count variant.** Counting edges gives m = e(F_a) + e(F_b) + k with e(F) = |F| − #paths.
   With exact piece counts this is the same inequality as step 4. With "at most p paths" it is
   weaker or equal, so the vertex form with exact counts is used throughout.
8. **Two cuts.** Choose the two least-used directions, so K = k_i + k_j ≤ floor(2m/N). The
   K + 1 pieces walk on the 4-cycle of quarters (each a Q_{N-2}). They alternate between the
   classes {00, 11} and {01, 10}, so

       m + 1 ≤ max_{p00+p11 = floor(K/2)+1, p01+p10 = ceil(K/2)} Σ_q g_{N-2}(p_q).

9. **Recursion for g itself.** Take a forest in Q_{n+1} with c' paths and f vertices. Cut it
   along its least-used direction, which carries k ≤ floor((f − c')/(n+1)) of its edges. That
   gives c1 + c2 = c' + k pieces with |c1 − c2| ≤ c', so f ≤ g_n(c1) + g_n(c2).
