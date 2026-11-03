# Sharpness and the number of endpoint exceptions

## Two counterexamples checked in Lean

Both examples contain the window

\[
(0,1,3,7,6,14,10),
\]

whose transition sequence is \(012032\).

| Example | Edges | Window start | Five internal counts | Relevant pair | Qualifying endpoint |
|---|---:|---:|---|---|---|
| First | 149 | 130 | \((8,6,10,3,8)\) | \(6+3=9\) | Initial vertex 18 |
| Balanced | 133 | 27 | \((11,4,13,5,12)\) | \(4+5=9\) | Final vertex 130 |

The first snake has endpoints 18 and 13; only 18 is at distance two from both
counted centres. The second has endpoints 25 and 130; only 130 has the two
required distances. The first qualifying window begins 130 edges from the
corresponding endpoint. In the second example, the corresponding endpoint is
106 edges after the window begins. These examples exclude an inference from
Hamming distance two to a short segment along the path.

The complete vertex sequences, induced-path condition, canonical shape,
individual pair counts and endpoint distances have passed Lean. The final
negative statements explicitly refute the following proposed strengthenings:

1. Every fitting \(012032\) window has pair sum at least ten.
2. Every fitting \(012032\) window whose two counts are at least four has
   pair sum at least ten.

Both examples have odd length. Their complete five-count vectors differ from
the vectors in the surviving periodic critical cycle. They therefore establish
local sharpness of the pair conditions and do not realize that entire cycle.
They also leave restrictions specifically to length 235 open. Neither example
improves the recorded 191-edge construction.

The search with the first window vertex required to be an endpoint returned
native UNSAT in 0.547 seconds, without any model or added cycle cut. This has
no checked contradiction certificate. The other searches produced the 149-edge
and 133-edge paths in 2.688 and 4.937 seconds, respectively, after adding valid
cycle cuts. No inference from a timeout or a disconnected model is used.

## Counting occurrences using the actual endpoint

The new written argument gives at most twelve assigned windows per endpoint,
or eleven when no counted window has that endpoint as its boundary. Each
window is assigned to one endpoint at distance two from both counted centres.
The argument applies to this larger geometric class; the pair-at-most-nine
condition supplies the assignment through the completed milestone 132 theorem.

The full proof is in audit/occurrence-geometry.md. Its essential steps are:

1. Orient the path from the endpoint and translate it to zero. The first
   neighbour forbids all but one selected distance-two vertex containing its
   coordinate. The remaining selected vertices correspond to pairs among
   eight coordinates.
2. The four alternating positions of each assigned window share one coordinate.
   When the endpoint is a window boundary, include it as the initial element.
   Intervals sharing different coordinates can overlap in at most one position.
3. Consecutive pairs \(\{u,v\}\) and \(\{u,w\}\) force \(\{v,w\}\) to
   be absent. Otherwise the intervening triple has three selected neighbours.
4. Count the available pairs and the missing pairs along these intervals.
   The two resulting inequalities leave one exceptional integer case,
   \((a,k,t)=(5,5,3)\). A missing-degree count excludes that case.

Here \(a\) counts the common coordinates used, \(k\) counts the maximal
intervals, and \(t\) counts missing pairs incident to those coordinates.
These quantities are used repeatedly in the proof and are unnecessary outside
that argument. With \(\delta=1\) for a counted boundary window and zero
otherwise, the conclusion of the written argument is \(W\le11+\delta\).

The following parts have passed Lean:

- The interval inequality
  \[
  |I|+2|\{\text{labels used by }I\}|+1
  \le\left|\bigcup_{r\in I}\{r,r+1,r+2,r+3\}\right|,
  \]
  under the stated separation between differently labelled starts.
- The earlier numerical estimate sixteen from that inequality and the pair
  capacity.
- The exceptional-case arithmetic and the conclusion \(W\le11+\delta\),
  conditional on the two geometric estimates and the exceptional-case estimate.

The complete occurrence theorem for actual snakes has not yet been checked
in Lean. Its remaining obligations are the coordinate-pair representation,
the construction of the intervals, the missing-pair argument, the path-block
count and their combination with the checked arithmetic. The bound twelve
must retain this verification status in summaries and the paper.

The written proof would give at most 24 low-pair windows after choosing one
qualifying endpoint for each start. A reduction to 22 would additionally require
excluding counted boundary windows at both ends. The native endpoint 0 result
is insufficient for that deduction. Neither budget is currently a completed
Lean theorem about actual snakes.

## Consequences for the length problem

The counterexamples show why occurrence restrictions are needed. The two
surviving cycle constraints from milestone 132 still limit the uniform-credit
formula, even after an occurrence allowance is supplied. Additional restrictions
or a revised comparison will be needed before any new length bound is claimed.

The recorded interval remains 191–235, with its documented independent-rebuild
limitation. The value 196 and optimality remain unresolved. The selected next
task is the actual-snake transfer for the occurrence argument. The paper remains
at revision 126; its next scheduled full revision is 136.
