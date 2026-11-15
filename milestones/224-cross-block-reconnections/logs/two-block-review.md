# Round 224: two simultaneous short replacements

The proposed bidirectional contact condition is necessary under the stated two-block model and the saved round-193 closure premise. It is a useful filter for simultaneous replacements; it does not establish that any such replacement exists.

## Precise assumptions and deduction

Let the original 191-edge bank path be \(P=(p_0,\ldots,p_{191})\). Choose

\[
0\le a<b\le c<d\le191,\qquad b-a\le33,\quad d-c\le33.
\]

Replace the blocks \([a,b]\) and \([c,d]\) by paths of exactly their original lengths, retaining their respective endpoint vertices at the same positions. Every position outside the two open interiors remains unchanged. Assume the simultaneous concatenation is an induced 191-edge path and can be extended by vertex 24 at its right endpoint.

Suppose the first replacement alone gave an induced path. Round 193's closure under one allowed replacement puts this intermediate path in the saved bank up to cube isometry and reversal. The second replacement is then another allowed move: its anchors and interval are unchanged, its length is at most 33, and its result is the assumed induced simultaneous path. Applying closure again puts the final path in the same bank family. Every member has both endpoints blocked, contradicting the extension by 24. Therefore the first replacement alone is invalid. Reversing the order proves the same for the second replacement.

Final inducedness ensures that each replacement is internally an induced path. It also prevents conflicts with unchanged outside vertices or retained anchors. Hence invalidity of the first replacement alone must come from a repeated vertex or an unwanted adjacency between its new interior and the original open interior of the second block. Conversely, the second replacement's new interior must repeat or be adjacent to a vertex in the original open interior of the first block.

Equivalently, each of the following two finite checks must find at least one pair:

\[
\begin{aligned}
&q_i=p_j\ \text{or}\ d_H(q_i,p_j)=1,
&&a<i<b,\ c<j<d,\\
&q_i=p_j\ \text{or}\ d_H(q_i,p_j)=1,
&&c<i<d,\ a<j<b.
\end{aligned}
\]

Here \(q\) is the final simultaneous path before appending 24. These positions are nonconsecutive, including when the blocks share one anchor. Thus the stated equality or adjacency invalidates the corresponding intermediate path.

## Anchors, indices and limitations

- A shared boundary anchor \(b=c\) is allowed. It must remain fixed, and it belongs to neither open interior. Overlapping interiors are outside this proof.
- Boundary blocks with \(a=0\) or \(d=191\) are allowed because the original global endpoint remains the replacement anchor.
- Equal lengths are essential to the simple index argument. With changed lengths, transport the second interval explicitly and revisit the closure hypothesis.
- The contacts concern original interior positions. A vertex can move from one block to the other, so do not replace these sets by vertices omitted from the final selected set. Equality is a valid contact and must not be discarded.
- Both contacts are necessary, not sufficient. The final joint path still needs every cross-block distinctness and nonadjacency check, and vertex 24 must have exactly its intended endpoint contact.
- The argument uses the complete native bank-closure census through 33 edges and blocked endpoints. Its generic iteration implication has a Lean proof with closure premises. This note does not add a Lean proof or replay the census.

The exact closure cutoff is 33. Round 194's cutoff 44 applies to one replacement followed immediately by endpoint extension; it does not prove closure under a sequence of 44-edge replacements. It cannot replace 33 in the two-step deduction above.

## The proposed concrete intervals

Using bank entry 123 and the same coordinate-7-to-bit-8 normalization as round 223, the original endpoints are 0 and 88. Vertex 24 is adjacent to 88. Its only other original contacts are the vertices at positions 7 and 143:

\[
p_7=28,\qquad p_{143}=56.
\]

Both contacts are adjacencies, and 24 is absent from the original path. The proposed intervals satisfy the strict-interior blocker requirement:

| Interval | Edge length | Anchors | Original coordinate-8 crossings inside |
|---|---:|---|---|
| \([0,16]\) | 16 | \(0,132\) | None |
| \([124,157]\) | 33 | \(356,251\) | Edge index 130 |

Thus both blockers are removed from their old positions, and neither is a retained anchor. The second interval includes both faces; it contains the crossing at index 130. Removing the two blockers is only necessary: the replacements must also avoid equality or adjacency to 24, except for the retained attachment vertex 88. The final endpoints 0 and 24 are both even, consistent with 192 edges. The two replacement lengths retain the original endpoint parity relations.

The literal vertices, contacts and crossing locations above were extracted from the saved bank, without a construction search. Bank SHA-256 is `0b973ddcd371680ad4efe07c01008c29437280514926daf1a67d99b6ba510edb`.

## Relation to earlier work

Round 192 already uses simultaneous-substitution implications: one substitution can force another because an intermediate selected path may be invalid. Its fixed alternate-square family and endpoint-extension census are narrower. Round 203 explicitly cautions that factoring a simultaneous block transformation need not produce valid intermediate snakes. The bounded review of round-192 through round-203 mathematical notes and relevant replacement sources found no explicit statement of this two-disjoint-block bidirectional contact consequence. This is a local repository observation, not a historical novelty claim.

Round 193's two-edge shortening census and round 195's interrupted shortened-state search concern different starting lengths and move families. The latter completed only six states and cannot supply an additional closure premise. Neither excludes the simultaneous two-block query considered here.

No solver, compiler, software tests or manuscript edits were performed. The deduction is conditional on the saved finite closure evidence and applies only to the fixed alignment, fixed anchors and equal-length short replacements specified above.
