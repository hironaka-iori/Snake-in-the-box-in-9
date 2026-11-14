# Orientation independence of the partner condition

The proposed equivalence is sound as a condition on one fixed candidate graph. It is a necessary condition for a completed assignment, and is not sufficient for that assignment to exist.

Fix one free-word parity. Let k be the number of its nonempty intervals. The established square geometry implies that a word shared by distinct intervals occurs on two singleton intervals at opposite corners. It cannot also occur on a third interval: that third interval would have to be a singleton opposite each of the first two corners. A multi-visit interval shares with no other interval of that parity.

Consequently, if r words are each used twice, those repetitions form r disjoint opposite-corner pairs, and the number of distinct assigned words is exactly k-r. An alphabet of 32 words gives
\[
r\ge k-32.
\]

Construct one fixed undirected candidate graph: its vertices are the singleton intervals, and an edge joins opposite-corner intervals when their current domains intersect and their equality is allowed. Multi-visit intervals are isolated if included as vertices. Every actual repeated pair is an edge, and the actual pairs form a matching. Therefore its maximum matching size must be at least k-32. When k <= 32 this particular condition is automatic.

## Equivalence with all subset inequalities

Choose one corner from each opposite pair for the chosen family C, and put all multi-visit intervals in C. The remaining singleton intervals form O. Each family has pairwise distinct actual words, and every candidate equality edge crosses between C and O. Set
\[
s=32-|C|,\qquad k=|C|+|O|.
\]
Initially require |C| <= 32, so s is nonnegative. For J contained in O, let N(J) be its neighbors among C in this same fixed candidate graph.

Add s auxiliary vertices on the C side, each adjacent to every member of O. Hall's theorem says that the augmented graph has a matching covering O exactly when
\[
|J|\le |N(J)|+s
\]
for every nonempty J contained in O. The empty-set inequality is automatic. A covering augmented matching uses at most s auxiliary vertices, so its original edges give a candidate matching of size at least |O|-s. Conversely, any original matching of that size leaves at most s members of O unmatched; pair those with distinct auxiliary vertices.

Thus all the subset inequalities are equivalent to
\[
\nu\ge |O|-s=k-32,
\]
where nu is the maximum matching size of the fixed candidate graph. Reversing the chosen side of either opposite-corner component changes C, O and s but leaves k and nu unchanged. This proves orientation independence, provided the same allowed equality edges are retained.

If an orientation has |C| > 32, it is already impossible by distinct-word capacity. The matching condition also fails: a matching has at most |O| edges, while k-32 > |O|. The auxiliary-vertex argument cannot use a negative s, so this case must be rejected separately.

## Scope and assumptions

- Equality candidates must describe the same symmetric graph under either orientation. In particular, an orientation-dependent incomplete partner list cannot be treated as the same graph. For the domain-based graph, use all allowed opposite-corner pairs with nonempty current domain intersection.
- The two bipartite components are independent as abstract graphs, so their matching sizes add. They still compete for actual word labels in the full assignment.
- Candidate edges record possible equalities separately. A matching need not admit distinct common words for its pairs, and unmatched intervals must also receive valid distinct words. Constraints between the two free-word parities remain. Hence the graph condition and the equivalent Hall inequalities do not establish satisfiability.
- For example, with an alphabet of two words, two singleton intervals at each of two opposite corners, and all four domains equal to the same singleton word, the candidate graph is K(2,2). Its maximum matching is two, meeting k-2 = 2 and every corresponding Hall inequality. No assignment exists, because the two intervals at either fixed corner must have distinct words. This illustrates the distinction between partner matching and an actual word assignment.
- The saved (4,7) even family has k=33 and requires at least one repeated pair. The (0,6) even and odd families each have k=39 and require at least seven. These thresholds agree with the spare-capacity table, independently of corner orientation.

This note contains a written proof using the standard finite Hall theorem. It asserts no Lean checking, native implementation, new search exclusion, or global snake bound.

## Self-contained matching justification

The covering criterion can also be proved by a finite alternating-path argument. Choose a maximum matching in the augmented graph. If an outside vertex is unmatched, follow unmatched edges toward the chosen side and matched edges back toward the outside side. No reachable chosen vertex can be unmatched, since the resulting alternating path would increase the matching size. Every neighbor of the reachable outside set is reachable and matched back into that set. Exactly the starting outside vertex lacks a matched predecessor, so the reachable outside set has one more vertex than its neighbor set. This contradicts the stated subset inequalities in the augmented graph. Conversely, any covering matching gives the required injection for every outside subset. Thus the equivalence does not require assuming that a successful candidate matching already supplies actual word labels.
