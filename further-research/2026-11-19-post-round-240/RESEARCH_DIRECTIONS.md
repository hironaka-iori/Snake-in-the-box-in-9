# Research directions for the next chat

These are continuation proposals based on the completed Round 240 checkpoint. The short seed-comparison identities below are written deductions included for planning; they have not been newly encoded in Lean or used in a search. No new global bound or snake construction is asserted.

## 1. Preferred immediate question: six affected counts

Let A be the adjacency operator of Q9, so (Af)(x) is the sum of f over the nine neighbours of x. The established five-count result says that a nonzero ternary function f cannot have Af supported on at most five vertices. The immediate question is whether support size six is possible.

For support sizes six through eight, f can be restricted to one parity side: if both parity restrictions were nonzero, their disjoint neighbour-count supports would each have at least six positions, giving at least twelve in total. A possible support must contain a distance-eight pair by the conditional eight-count result.

The distance-eight graph on that support is an induced subgraph of the folded cube of order nine. It is bipartite for at most eight vertices. Each connected k-point component has generator coordinates using at most k-1 independent labels. The original cube distance between two such points whose generator coordinates differ in t positions is

\[
d=\begin{cases}t,&t\text{ even},\\9-t,&t\text{ odd}.\end{cases}
\]

Use this to organize the connected six-point configurations. Start with row differences, repeated neighbourhoods, and actual automorphisms of the distance matrix. The whole-support stars are already excluded in the structural note. Avoid assuming that every abstract bipartite graph is realizable by these cube coordinates.

For missing positions p_i, write w_i=(Af)(p_i). The necessary antipodal equations are

\[
Hw=315s,\qquad s_i\in\{-1,0,1\},\qquad |w_i|\le9,
\]

where H has diagonal 128 and entries -16, 8, -10, 35 at pairwise distances 2, 4, 6, 8. Retain the amplitude bound. The explicit eight-point configuration admits nonzero unrestricted integer solutions with amplitude 21, so a general unrestricted zero-solution lemma is false.

Connected cases alone are insufficient. Distinct distance-eight components still have matrix entries -16, 8, or -10 between them. A valid component argument must bound or incorporate these terms. In block notation the first component satisfies H_11 w_1 = 315 s_1 - H_12 w_2; its effective right-hand side is generally no longer 315 times a ternary vector. This is the precise obstruction to applying the whole-support star proof to an isolated component of a larger support.

An alternative exhaustive description for six points fixes a distance-eight pair and describes four other positions by sixteen column patterns across eight coordinates. It gives 490,314 weak compositions before invalid descriptions and symmetries are removed. This is a derived coverage size, not a completed enumeration. Prefer a structural reduction first, and estimate resources before considering exhaustive arithmetic.

If a bounded matrix solution survives, reconstruct f at all 512 vertices using the saved inverse. Every value must be ternary and its adjacency sums must reproduce the proposed support. A surviving antipodal system alone is not a recovery counterexample.

## 2. Connect reconstruction directly to a longer snake

Fix a verified 191-edge seed with vertex set S, hence |S|=192. For a proposed 192-edge snake let T be its 193-vertex set. Write f=1_T-1_S and w=Af. This uses the same count-difference equations, now with information from an actual seed.

The following necessary identities and restrictions follow directly from membership, cardinality, and the fact that every cube vertex has nine neighbours:

\[
f(x)\in\{-1,0\}\ (x\in S),\qquad
f(x)\in\{0,1\}\ (x\notin S),\qquad
\sum_x f(x)=1,
\]
\[
\sum_x w(x)=9,\qquad
-c_S(x)\le w(x)\le9-c_S(x),
\qquad c_S(x)=(A1_S)(x).
\]

The sum identity holds because each term f(x) occurs in exactly nine neighbour sums. The interval follows from c_T=c_S+w and 0 <= c_T <= 9. These seed-dependent intervals and membership signs are stronger than treating every unknown independently as an integer between -9 and 9.

There is also a useful parity refinement. A 191-edge seed has 96 vertices of each parity. Choose an orientation in which the target has 97 even and 96 odd vertices. Then the even and odd sums of f are 1 and 0, respectively, so the odd and even sums of w are 9 and 0, respectively. Reverse the parity labels for the other orientation. This follows because adjacency changes parity. It should be encoded and checked before use in a numerical search.

For x selected in T, the value c_T(x) is its degree in the induced graph on T. Require degree two except at exactly two vertices of degree one, and require connectedness. These conditions exclude a path together with disjoint cycles. A resulting connected induced graph with those degrees is a path, whose ordering can then be extracted and directly verified.

There is a lower starting point specific to these saved seeds. The recorded fixed-colour exclusions in the manuscript's subsection "The complementary fixed-minority construction" require a 192-edge candidate to change both parity classes of every saved seed. Hence both parity restrictions of f are nonzero. Five-count recovery applies separately to them, and their neighbour-sum supports lie on opposite sides. Therefore

\[
|\operatorname{supp}(w)|
=|\operatorname{supp}(Af_{\mathrm{even}})|
+|\operatorname{supp}(Af_{\mathrm{odd}})|\ge6+6=12.
\]

This is a written consequence of the existing five-count theorem and the saved native/written construction exclusions. It inherits those evidence limits and has no new Lean assembly in this handoff. It is specific to comparing a 192-edge candidate with a saved seed, and it does not raise the general six-to-nine support interval for arbitrary binary selections. No search for a seed-compatible improvement with at most eleven changed counts is needed under these premises. If unrestricted six-count recovery were proved, the same argument would raise this seed-comparison threshold to fourteen.

This suggests a bounded future experiment: investigate count-change supports starting at twelve while enforcing the seed-specific signs, the sum conditions, and the full inverse. Compare its effectiveness with direct vertex replacement. A count-profile parameterization may improve a search, but that has not been demonstrated.

Do not identify the size of the support of f with the size of the support of w. The inverse can spread a sparse count change across many vertex changes. The existing saved-seed comparison requires at least six deletions and seven additions for a 192-edge candidate, so at least thirteen changed memberships. It gives no equality between those thirteen changes and the number of affected neighbour counts. Conversely, a longer snake need not have a sparse count change relative to any saved seed. Excluding all small supports therefore excludes only that construction family.

## 3. Use symmetry at the correct scope

For a fixed seed, cube automorphisms that preserve the seed as a set also preserve its neighbour-count profile and the seed-comparison conditions. They can identify equivalent proposed changes. A cube isometry that moves the seed to a different set cannot be used to identify two changes while keeping the seed fixed. Either move the seed and change together or use the seed's stabilizing automorphisms.

Path reversal does not change a vertex set or its count profile. It can reduce redundancy in ordered path searches, but it contributes no new count-profile equivalence by itself.

Whole-snake symmetry is a possible constructive restriction, not a requirement of all longest snakes. Search for a useful transformation of the entire path or selected set, and state exactly what it preserves. For coordinate histories, any transformation must preserve all cross-part nonconsecutive distances as well as consecutive steps. A failed symmetric family leaves asymmetric constructions open.

The useful lesson from the eight-point example is specific: symmetry can reduce the matrix to character equations and reveal divisibility restrictions. Bipartiteness alone is weaker. Look for an actual commuting family of permutations or repeated-row structure before introducing Fourier notation.

## 4. A proof-completion alternative

The literal arithmetic for four and five missing counts is already accepted in Lean. The missing whole-cube proof must extract and index the exceptional positions, split parity cases, identify the inverse coefficients at antipodes, and establish coverage by the accepted matrices. Prioritize a small complete bridge, beginning with four counts if that makes the classification manageable.

A successful bridge changes the verification status of an existing numerical threshold. It does not by itself improve the threshold or construct a longer snake. Avoid regenerating hundreds of accepted arithmetic cases merely because a new chat begins.

The written Walsh classification for the eight-point generator cube and the whole-support star proof are smaller candidate Lean tasks. They may provide reusable tools for the next structural cases. Their finite explicit witness and their universal classification have different scopes.

## 5. Return to construction if reconstruction stops helping

Revisit the Q6-to-Q7 and Q7-to-Q8 constructions as concrete samples. Record the parent paths, retained pieces, coordinate crossings, compatible overlaps, and the exact conditions excluding chords. Seek a transformation that is proved for an identified family, then assess its Q8-to-Q9 output. The numerical sequence alone gives no recurrence.

The saved 98-edge parent has a recorded one-crossing ceiling of 191 within its isometry class. The specified two-block family is excluded through width 46. To avoid repeating those searches, change a documented restriction: parent class, block lengths, number or arrangement of replaced pieces, or simultaneous changes in both parity classes. Recheck the original family definition before claiming a new search lies outside it.

Partial greedy growth remains an optional completion heuristic after a structural change. It is not the main route at this handoff. Greedy failure supplies no exclusion theorem.

## 6. Expected outcomes and what they mean

| Outcome | Meaning |
| --- | --- |
| Every six-position support is excluded, with complete coverage | Recovery improves to 506 observed counts; the minimum changed-count support rises to at least seven. No snake-length improvement follows automatically. |
| Only a connected family is excluded | A useful restricted lemma; disconnected cases and other shapes remain. |
| A bounded antipodal solution has a nonternary full inverse | More inverse equations are needed; recovery remains unresolved. |
| A valid ternary f has six, seven, or eight affected counts | A recovery counterexample disproves the working minimum-nine conjecture. It does not automatically yield a snake. |
| A seed-compatible reconstruction gives a connected induced path on 193 vertices | A verified 192-edge snake would improve the lower bound. Preserve the explicit sequence and complete checks before announcing it. |
| The Lean cube bridge succeeds | Stronger verification of an existing theorem, with no numerical gain. |
| Structural cases grow without useful reduction | Record the exact unresolved cases and switch to the construction or proof-completion route. |

My qualitative expectation is that additional structural exclusions are more immediately attainable than a longer snake. The eight-point bounded classification supports investigating the minimum-nine conjecture, but it is insufficient evidence to predict a universal proof. The probability of a 192-edge construction cannot be inferred from these local results. No numerical probability or target date is justified.

Finish one coherent question per round, save both successful and unsuccessful evidence with its scope, and retain a concrete reason for the next step. No work in this file is authorized to start in the paused old chat.
