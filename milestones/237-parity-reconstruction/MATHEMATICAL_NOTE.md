# Round 237: majority exchanges and reconstruction with missing counts

This round resumes an unfinished local checkpoint. Its original numerical searches and loose compiler logs were preserved. The resumption reconstructs their finite inputs, completes the interrupted numerical-cut replay under the retained resource limits, and binds the cube and path proofs to current source hashes. No longer snake is found.

## Construction question

A 192-edge snake has a 97-vertex majority parity class and a 96-vertex minority class. For each of the 145 saved 96-vertex sets \(B\), consider
\[
U=(B\setminus\{d\})\cup\{a,b\},
\]
where \(d\in B\) and \(a,b\) are distinct vertices of the same parity outside \(B\). The hypothesis was that one such majority exchange might permit a longer snake, with all minority vertices, endpoints and ordering free.

For a one-parity set \(U\), join two members when an opposite-parity vertex has exactly those two neighbours in \(U\). Count distinct partners even if two labels witness the same edge. A snake with majority class \(U\) exists exactly when this simple graph has a Hamiltonian path. The forward implication takes every second path vertex. Conversely, interleaving a Hamiltonian order with one witnessing label per edge gives distinct labels, because a label witnesses only one unordered pair. The two-neighbour condition excludes all chords.

## Pruning and explicit cut witnesses

If \(r\) majority positions are missing from a partial proposal, deleting their positions from a final Hamiltonian order leaves at most \(r+1\) runs. Each run contributes two missing incidences, including a singleton. Edges within a run retain their labels after restriction. Extra graph edges can only reduce the total deficit, giving
\[
2I+L\le 2r+2.
\]
Here \(I\) and \(L\) count isolated vertices and leaves. At the final set there can be no isolated vertex and at most two leaves.

For a complete majority set and arbitrary subsets \(S,T\), a stronger necessary inequality is
\[
2|S|\le 2|T|+2+e(S,U\setminus T),
\]
where \(e\) counts ordered graph edges. The path degrees at \(S\) sum to at least \(2|S|-2\). At most \(2|T|\) of these incidences can end in \(T\); each remaining incidence is counted by \(e\). This proof allows \(S\) and \(T\) to overlap.

Two previously completed independent enumerations agree on the 679 surviving descriptions among 177,062,400 initial descriptions. They specify 623 distinct sets. Every surviving set violates the directed-cut inequality for saved explicit subsets. The positive excesses 2, 4, 6 and 8 occur 161, 291, 167 and 4 times. The resumption audit reconstructs all 623 graphs and inequalities, maps their masks and subsets to the original declarations, and verifies the 679 descriptions. It does not rerun the full 177-million-description enumeration.

All 623 closed numerical inequalities now have accepted Lean receipts. The original groups of 25 exceeded the current memory limit; groups of five with synchronous elaboration passed. Their literal statements and numerical inputs are unchanged. The general path-index cut theorem and partial-deficit arguments are separate checked statements. The complete mathematical connection between the numerical row counts and the path theorem is written in spectral/BRIDGE_REVIEW.md. Its full proof-assistant reindexing assembly remains open. Thus the entire saved-family exclusion is not described as an end-to-end Lean theorem.

A separate necessary-degree model was previously natively infeasible for all 145 starting classes. It selects 97 majority and 96 minority vertices, retains exactly 95 of the old majority class, and enforces selected degrees two except for two majority endpoints. All unselected degrees are unrestricted. The resumption audit reconstructs every archived model and selection guard. These 145 infeasibility conclusions remain solver evidence without a contradiction replay.

## Consequence for a longer snake

The previous majority cover excludes overlap 96; this round excludes overlap 95. Hence the majority intersection with a saved seed is at most 94. Earlier minority covers bound the other intersection by 92, giving
\[
|P\cap Q|\le94+92=186.
\]
A saved seed has 192 vertices and a proposed 192-edge snake has 193. At least six old vertices must be omitted and seven new vertices introduced. Pulling a candidate back by a cube isometry proves the same statement for every isometric seed copy. This restriction depends on the recorded finite covers and gives no global upper bound.

## Full cube reconstruction and two missing counts

For an integer function \(z\) on the actual nine-bit cube, let \(b(v)\) be the sum of \(z\) at the nine neighbours of \(v\). The inverse from round 236 has weights 35, -10, 8, -16 and 128 at distances 1, 3, 5, 7 and 9. This round supplies the complete recursive-cube proof, rather than leaving the cube coefficient identity as a premise. The monolithic finite reduction exceeded the memory limit. Sixteen exhaustive 32-case prefix modules establish the same coefficient calculation; the algebra then gives the actual-cube inverse and injectivity.

If \(z\) is the difference of two binary selections and \(b\) is zero except possibly at distinct vertices \(p,q\), write \(x=b(p)\), \(y=b(q)\). Applying the inverse at the antipodes gives
\[
128x+cy=315s,\qquad cx+128y=315t,
\]
where \(c\in\{0,35,-10,8,-16\}\), \(s,t\in\{-1,0,1\}\), and \(x,y\) are integers between -9 and 9. The finite integer cases force \(x=y=0\). The inverse then forces \(z=0\). Therefore the neighbour counts at any 510 of the 512 vertices uniquely determine a binary selection. The split actual-cube proof and this recovery theorem have passed the fresh guarded compiler.

For a selection known to lie in one parity side, the counts on that same side are automatically zero. Consequently any 254 of the 256 opposite-side counts suffice, by the two-missing-count theorem. This is a written specialization. It does not make a partial construction with many unspecified counts uniquely determined, nor does reconstruction enforce connectedness.

## Current bounds and continuation

The contributor source at revision 478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088 states the universal 231-edge theorem and includes successful final assembly and standard-axiom audit records. Those exact Git objects were inspected and archived. A fresh independent rebuild of the entire contributor dependency closure remains pending. The maintained interval is now \(191\le a(9)\le231\). The historical 233 and 235 derivations remain in the paper with their original constants and provenance.

The four-replacement minority cases 7, 6 and 0 remain unresolved from round 236; class 139 is excluded at that exact count. The other 141 classes were not queried at four replacements. No status is upgraded by the present majority-side result. Future construction searches can use both parity overlap restrictions and the neighbour-count consistency conditions.

The user has requested full work through rounds 237, 238 and 239. Publish this checkpoint, continue to 238, and stop after 239. The earlier PAUSED.md records a superseded interruption. The next full-source manuscript review remains due at round 240.
