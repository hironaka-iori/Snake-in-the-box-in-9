# Independent review: existing alpha rules added to the three-centre CNF

Outcome: the current rule set is valid for every consecutive internal-centre window of a genuine Q9 induced snake. No missing shape assumption or counterexample was found. These are global snake consequences used to strengthen a local necessary-condition relaxation; they need not hold for an arbitrary disconnected selected set satisfying only the old local degree clauses.

## Exact project statements

- AggregateSingletonBound.lean, localAlpha_positive: every snake vertex has localAlpha>=1, by singleton_at_vertex. Its localAlpha definition sums the same36 singleton-square indicators used here.
- UpperBound251.lean, adjacent_internal_alpha_one_impossible: two selected adjacent vertices i,j cannot both have alpha1. Both indices satisfy0<i<m and0<j<m.
- UpperBound248.lean, adjacent_internal_one_two_impossible: under those same internal-index and adjacency hypotheses, alpha(i)=1 andalpha(j)=2 is impossible.
- AdjacentOneThreeExclusion.lean, adjacent_internal_one_three_impossible excludes(1,3) with the same hypotheses. alpha_one_internal_neighbor_ge_four combines positivity and all three exclusions to prove alpha(i)=1 implies alpha(j)>=4. Swapping i,j gives the reverse orientation.
- UpperBound245.lean, no_three_consecutive_internal_twos: for a starting index r with r+4<=m, the centres r+1,r+2,r+3 cannot all have alpha2. That condition is precisely the existence of their preceding and following path vertices. It is not limited to the repeated-direction shape. The top theorem resolves the normalized shape cases through its imported geometric lemmas.

These are source theorems with the hypotheses stated above, not conditional AllRefuted certificate assumptions. This review did not newly recompile their mathlib proof closures. The added alpha-counter-to-CNF bridge is likewise not newly Lean-verified.

## Current encoding audit

E.by_centre preserves each unaggregated singleton indicator at weight21. The other unaggregated terms have weights12,2 or1, so filtering w==21 extracts exactly the36 singleton indicators, including repeated constant literals from fixed-path folding. The explicit36 check guards the current layout. This should be revisited if future score definitions introduce another weight21 term.

The binary PB comparisons encode alpha<=k for k0..3. Thus AND(le1,not le0) is alpha1 and AND(le2,not le1) is alpha2. The emitted clauses enforce alpha>=1, both directions of alpha1=>neighbor>=4 and the forbidden222 triple. Every pair/triple examined consists only of consecutive centres in E.path[1:-1], so all source internality and adjacency premises hold. The endpoints of a fixed window must not automatically be treated as global snake endpoints.

Appending new geometric rules leaves old initial clause IDs unchanged. Old learned IDs shift by delta, so remapping every old hint ID>old_base_count by delta is exactly correct. New proof tails then refer to the strengthened base followed by that remapped old prefix. I reconstructed both full clause lists and independently checked the complete combined proofs.

## Actual bounded outcomes

Both formulas add857 rule/counter clauses. The full checked results are:

- 0120:35,136 RUP steps and3,330,640 hints, no empty clause and no SAT model:UNKNOWN.
- 0123:32,946 RUP steps and3,244,144 hints, no empty clause and no SAT model:UNKNOWN.

These include the verified remapped old prefixes, not just the newly generated tails. Reproduce with review_alpha_rules.py; exact JSON results are in alpha_rules_independent_review.json. No new numerical upper bound follows from these unresolved searches.
