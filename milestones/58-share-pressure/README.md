# Milestone 58: forced-absence share bounds

This round continues the empty-square route. The main result is a direct geometric lower bound for the empty-square share, with 76 eight-transition instances checked in Lean. The exact exploratory minimum rises from 49/12 to **617/150**. Its conditional edge estimate still has integer part 235. The contributor-checked global interval remains **191 <= a(9) <= 235**; the exact optimum is unresolved.

## The geometric argument

Let S be the vertex set of a snake and W=(x_0,...,x_8) a consecutive segment. Each of x_1,...,x_7 already has two selected neighbours in W. Every other neighbour of these seven vertices must therefore be absent from S. Write D for this forced-absence set and U=V(Q_9)\D. Then S is contained in U.

For a vertex q, let e_A(q) count the coordinate squares through q whose four vertices lie outside A, and let d_A(q) count its neighbours in A. For a selected centre x, define

\[
\sigma_A(x)=\sum_{q\sim x}\left\lfloor\frac{12e_A(q)}{d_A(q)}\right\rfloor.
\]

Every denominator is positive because x is selected. The inclusion S⊆U gives e_U(q)≤e_S(q) and d_S(q)≤d_U(q). Consequently

\[
\sigma_U(x)\le\sigma_S(x),\qquad
L(W):=\sum_{i=3}^{7}\sigma_U(x_i)
\le\sum_{i=3}^{7}\sigma_S(x_i).
\]

This is the **forced-absence share bound**. Computing its left side requires only the known segment. U is a superset used to obtain a lower bound; U need not itself be a snake. The calculation retains the full degree upper bound d_U(q), rather than replacing every denominator by nine. Repeated square contributions follow the existing corner-share definition and its global charging budget.

The Lean proof first establishes monotonicity under enlarging the selected set, with explicit positive-denominator hypotheses. It then proves forced absence from the degree-at-most-two condition and transports each finite calculation through an arbitrary coordinate permutation and translation. No singleton-count assumptions are needed for these new geometric inequalities.

## Complete eight-transition calculation

All 132 canonical induced eight-transition shapes were independently enumerated. Exactly 76 have positive L(W), and the largest value is 18. Their finite calculations and arbitrary-snake consequences are in `lean/Geometry/`. The universal proof and transport are in `ForcedShare.lean` and `ForcedShareBridge.lean`. `data/lean-audit.json` records the successful build and dependency checks.

The independent verifier enumerates all 4,608 square faces, reconstructs every forced-absence set, and checks every denominator and summand. It also verifies 131 stored snakes and 48,208 oriented eight-transition windows. Of these windows, 32,906 receive positive geometric credit. The examples contain 110 of the 132 shapes; the smallest observed actual-share excess above the bound is 136. These examples are consistency checks; the arbitrary-snake results come from the proofs.

## Effect on the finite model

The new geometric credit is combined with each existing five-centre share lower bound by taking their maximum. Adding the two bounds would charge the same share twice without justification.

| Model | Exact normalized minimum | Potential range | Attaining cycle length | Conditional integer bound |
|---|---:|---:|---:|---:|
| Previous combined model | 49/12 | 650 | 12 | 235 |
| New numerical count-specific candidate | 94/23 | 15,240 | 23 | 235 |
| Forced-absence geometry | 617/150 | 3,122 | 20 | 235 |
| Geometry and the new candidate | 617/150 | 3,122 | 20 | 235 |

The geometric update strengthens 1,766,089 of 3,042,328 transitions. For every updated model, an independent exact-integer check verifies every edge potential inequality and a cycle attaining the stated minimum. The geometric model has integer weight mean 2468/5, with edge weight 120b+L. The existing overlap and boundary calculation gives the conditional estimate

\[
m\le\frac{2\,759\,699}{11\,734}<236.
\]

The previous twelve-step cycle gains 64 geometric share units. The replacement twenty-step cycle has 32 total recorded share units. Thus the direct calculation addresses the previously uncharged cycle, although a different cycle still limits the result. The geometric model already incorporates inherited numerical exclusions and share candidates; their complete proof replay and the complete graph-to-snake assembly remain pending. The finite potential checks are independent exact computations, not a Lean replay of the entire graph.

## Count-specific screening and its limitations

Before the geometric calculation, the full minimum family at mean 49/12 was extracted: two components of twelve states and sixteen edges each, giving 24 states, 32 edges and twelve five-centre patterns. Removing any one of those patterns destroys every cycle in this family.

All twelve ordinary controls have independently checked local forests. Share-cap-95 screening returns one numerical INFEASIBLE result and eleven UNKNOWN results. The resulting proposed share-96 inequality has directions (a,b,c,d,a,e) and counts (2,A,4,2,B), where the five letters are distinct and A,B lie in [6,21]. It has no Lean refutation replay. Adding it after the geometric update does not improve the minimum, so replaying it is not the immediate priority.

Six broader share tests, using joint count constraints or dropping count caps, all return UNKNOWN. They establish no exclusion and no share lower bound. A local forest also does not establish extendability to a complete snake.

## A limitation of redistributing the same five-centre charge

The individual forced contributions also permit a simple weighted relaxation. Write g_i for the five individual geometric bounds and H for the larger of their sum and the existing total-share bound. For nonnegative c,v_i with 5c+sum(v_i)=5, weights c+v_i give the lower bound cH+sum(v_i g_i). This follows by applying c to the total-share inequality and v_i to the individual inequalities.

The six vertices of this weight simplex are the uniform choice and the five choices concentrating weight five on one centre. On the saved twenty-step cycle their mean integer weights are, respectively,

\[
\frac{2468}{5},\quad\frac{987}{2},\quad493,\quad
\frac{987}{2},\quad\frac{989}{2},\quad\frac{987}{2}.
\]

Thus every fixed weighting in this relaxation has minimum cycle mean at most 989/2. With the existing seven-window boundary correction, excluding m=235 would require

\[
\mu>\frac{9400}{19}>\frac{989}{2}
\]

even if the potential range were zero. The finite coefficients are independently checked, and Lean checks the convex-combination ceiling and the boundary arithmetic. This rules out obtaining 234 solely by optimizing these fixed weights under the current accounting. It does not rule out stronger geometric information, count-dependent weights with additional accounting, or a sharper boundary argument.

## Reproduction and continuation

- `scripts/critical.py`, `prioritize.py`, `probe.py`, `generalize.py`: source-family extraction and numerical screening.
- `scripts/forced_geometry.py`: explicit forced-absence calculations for all 132 shapes.
- `scripts/prepare_geometry.py`, `replay.py --resume`, `audit_lean.py`: generate, check and audit the geometric proofs.
- `scripts/apply_candidate.py`, `apply_geometry.py`: construct the comparison models and exact potentials.
- `scripts/verify_geometry.py`: independent geometric, critical-family, witness and potential checks.
- `scripts/weighted_ceiling.py`, `lean/WeightedCeiling.lean`: the restricted weighting ceiling and its conditional arithmetic.
- `data/verification-geometry.json`, `data/lean-audit.json`: verification receipts with explicit scope.

The next research target is to strengthen the forced-absence information on the replacement family at mean 617/150. The most direct extension is to retain one additional transition of the known segment, while continuing to charge its last five internal centres. This preserves the fivefold overlap budget and can expose additional absent vertices and empty squares. The weighted ceiling above makes this a better next test than optimizing the same five-centre coefficients alone.

This is research round 2 of 10 after manuscript revision 56. The paper and its open editor mirror remain unchanged and synchronized; the next scheduled full paper revision is milestone 66. The compilation limitation recorded in milestone 56 remains unresolved.
