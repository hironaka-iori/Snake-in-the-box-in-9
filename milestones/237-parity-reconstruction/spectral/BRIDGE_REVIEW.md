# Review of the numerical cut and path-count connection

The mathematical connection is valid. No missing hypothesis was found in the directed-cut inequality or the partial-set degree condition. The existing numerical cut statements do not, by themselves, constitute a complete Lean theorem excluding an induced path: the numerical row counts still need to be connected to the indexed counts in `Cut237.induced_path_cut_bound`.

This review read the complete sources `majority/CubeCut.lean`, `spectral/Cut237.lean`, `spectral/PartialDeficit237.lean`, `spectral/ContractedDegrees237.lean`, the relevant earlier colour-contraction source, the existing `spectral/CutGeometry237.lean`, the two enumeration programs, and the certificate generator. No compiler or solver was run during this review.

## Exact meaning of a numerical row

Let (U\subseteq\{0,\ldots,511\}) be the selected one-parity set. Its numerical mask is

\[
M=\sum_{u\in U}2^u.
\]

Let (G(U)) be the simple graph on (U) in which distinct vertices (u,w) are adjacent precisely when a cube vertex (z) has exactly (u,w) as its selected neighbours in (U). Let the duplicate-free lists `s` and `t` represent subsets (S,T\subseteq U), and let `inside = encode t`.

The definition `escapes M inside u`, for (u\in U), equals

\[
|\{w\in U\setminus T: u\text{ and }w\text{ are adjacent in }G(U)\}|.
\]

The reasons are as follows.

1. Each axis is a distinct power of two among (1,2,\ldots,256). Flipping two distinct axes sends (u) to a distinct vertex (w) at distance two. Every distance-two vertex arises from exactly one unordered axis pair. The condition `i < j` therefore enumerates it once.
2. If a distinct pair has a common cube neighbour, its distance is two. For the pair obtained by flipping axes (i,j), its only common neighbours are (u\mathbin{\mathrm{xor}}i) and (u\mathbin{\mathrm{xor}}j). A common neighbour must flip one of the two differing coordinates; both choices work.
3. The `selected` and `inside` bit conditions say exactly (w\in U\setminus T). The bitwise equality with `bit u ||| bit w` says that the chosen common neighbour has precisely those two neighbours in (U). The disjunction considers its two possible labels. Even if both labels work, the target is counted once.
4. The outer sum and inner filtered lengths count these distinct targets. There are no diagonal pairs because `i < j` forces (i\ne j).

The selected mask must represent the complete one-parity set being considered. The actual certificate generator uses the explicit set ((B\setminus\{d\})\cup\{a,b\}), whose members lie below 512. No assertion about arbitrary high bits of an unconstrained mask is needed.

Consequently,

\[
\sum_{u\in S}\operatorname{escapes}(M,\operatorname{encode}(T),u)
=e(S,U\setminus T),
\]

where (e) counts ordered simple edges. The lists may represent overlapping subsets (S,T). Overlap causes no double counting within an ordered row and does not invalidate the inequality.

## Transfer to an actual path

Suppose an induced path of length (2k>0) has complete even-position set (U). Write (q_i=p_{2i}), (0\le i\le k). The path's injectivity makes (i\mapsto q_i) a bijection from these indices to (U). The odd-position vertex (p_{2i+1}) has exactly (q_i,q_{i+1}) as its neighbours in (U), so successive indices are partners in the sense of `ContractedDegrees237.Partner`.

Set the flags in `Cut237` as follows: `s i` records (q_i\in S); `t (i+1)` records (q_i\in T); and the two boundary flags `t 0` and `t (k+2)` are true. Injectivity and completeness give the three reindexing identities

\[
\begin{aligned}
\operatorname{total}_{k+1}\mathbf 1_S&=|S|,\\
\operatorname{total}_{k+1}\mathbf 1_T&=|T|,\\
\operatorname{total}_{k+1}\operatorname{cutRow}&=e(S,U\setminus T).
\end{aligned}
\]

For the third identity, the numerical row proof above identifies the target vertices, while the bijection (j\mapsto q_j) identifies them with the target indices counted by `edgeIndicator`. Symmetry of cube adjacency identifies the orientation used by the numerical mask with that in `Partner`.

The checked path-side inequality then gives

\[
2|S|\le 2|T|+2+e(S,U\setminus T).
\]

There is also a direct proof: the path degrees at sources in (S) sum to at least (2|S|-2). Destinations in (T) receive at most (2|T|) of these incidences. Each remaining incidence is a distinct ordered edge counted by (e(S,U\setminus T)). The two sets need not be disjoint.

When `violated M s t = true`, its initial conjunction checks that `s` and `t` are duplicate-free lists of selected vertices below 512. Their lengths are therefore (|S|,|T|). Its last conjunction states the strict reverse of the displayed inequality, using the exact numerical row sum. This is incompatible with the hypothesized path.

Thus the complete mathematical interpretation is: a verified `violated` value, together with the stated mask/set interpretation, excludes every induced path whose complete even-position set is (U). There is no fixed-endpoint, fixed-order or fixed-minority-set restriction in this implication.

## Partial sets and the pruning thresholds

For (W\subseteq U), delete the positions in (U\setminus W) from the even-position order. If (m=|U\setminus W|), at most (m+1) nonempty runs remain. Every edge of a run retains the same intervening label: restricting the selected set removes other vertices, while the two selected neighbours of this label remain. Hence these runs form a spanning union of paths in (G(W)).

An isolated run contributes two units of degree deficit, and a nontrivial run also contributes two, one at each end. Extra graph edges can only decrease each vertex's quantity \(\max(0,2-\deg(v))\). Therefore

\[
2I(W)+L(W)\le 2m+2.
\]

The definitions of `PartialPartner` and `deficiency` match this argument: the former restricts the label condition only to retained positions, and the latter assigns two to a retained isolated vertex, one to a retained nonisolated vertex with at most one partner, and zero otherwise. The ordering-to-vertex-set reindexing remains a separate interpretation step for the numerical counts.

In the majority-exchange search, deleting one vertex from a 96-set leaves 95 vertices; the proposed final majority has 97, so (m=2) and the threshold is six. After one insertion the set has 96 vertices, so (m=1) and the threshold is four. At the final 97-set, a nontrivial spanning path has no isolated vertex and at most two leaves. The separate no-isolate condition is necessary: the inequality (2I+L\le2) alone would permit one isolated vertex. Both enumerators apply the stronger final condition.

The original dynamic enumeration maintains simple degrees by tracking when the number of labels for a pair changes between zero and nonzero. The independent enumeration rebuilds label masks and avoids counting the second common label twice. Both implementations use the simple contraction graph, as required by the proof. Their enumeration coverage remains computational evidence.

## Exact proof-assistant boundary

The saved compiler logs report accepted path-side statements for `ContractedDegrees237`, `PartialDeficit237` and `Cut237`, with only the listed standard axioms. This review did not rebuild those modules or their dependencies.

The pre-existing source `CutGeometry237.lean` attempts six relevant results: uniqueness of the ordered axis pair; existence of that pair from a common neighbour; classification of its two labels; list-mask membership; neighbour-mask membership; and exact pair-mask semantics. No accepted compiler record for that source was present at the time of inspection. The parent task should use the actual subsequent compilation outcome.

Even if those six lemmas pass, the following machine-checked connections are still absent from the inspected source:

- An equality between the filtered/summed `escapes` computation and the number of distinct eligible targets.
- The three population and row-count reindexing identities under the injective even-position order.
- A theorem combining `violated = true` with `induced_path_cut_bound` to derive the contradiction for the actual labelled cube.

The exact numerical inequalities can be kernel-checked independently of these missing connections. Completing all 623 numerical checks would certify those 623 closed numerical statements. It would not by itself certify the complete saved-family exclusion, because the graph interpretation, the enumeration-to-certificate mapping and the native enumeration coverage retain their separate scopes.

A small theorem taking all three numerical-to-indexed count identities as premises would merely package the remaining obligations. No such wrapper is supplied as a purported completion. The written proof above supplies the mathematical justification; the outstanding Lean connections are explicit.
