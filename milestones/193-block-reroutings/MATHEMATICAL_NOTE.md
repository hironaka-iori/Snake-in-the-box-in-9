# Round 193: contiguous replacements and closure of the saved bank

The construction search still has no snake longer than 191 edges. This round establishes a restricted computational barrier: every length-preserving replacement of a contiguous block of at most 33 edges in any of the 131 saved snakes stays in the same bank up to cube isometry and path reversal. Blocks of one edge have no alternative. There are 43094 valid moves for lengths 2--33; the counts include repeated outcomes. None changes the crossing positions of a coordinate used exactly twice. Every bank representative has both endpoints blocked.

## Replacement criterion

Let \(P=(p_0,\ldots,p_L)\) be induced, with \(0\le i<j\le L\), and retain \(C=\{p_0,\ldots,p_i\}\cup\{p_j,\ldots,p_L\}\). Let \(R\) be an induced path between \(u=p_i\) and \(v=p_j\), with interior \(I\). The concatenation is induced exactly when

\[
I\cap\left(C\cup\bigcup_{z\in C\setminus\{u,v\}}N(z)\right)=\varnothing.
\]

Every collision repeats a retained vertex, and every forbidden edge is a chord. Conversely, pairs within the replacement are controlled by its inducedness, retained pairs keep their original relationships, and the displayed condition handles all remaining pairs. The anchors are excluded from the neighbourhood mask because their intended replacement edges must remain. Boundary blocks \(i=0\) and \(j=L\) satisfy the same argument. Writing \(\ell\) for the replacement length gives \(\ell\equiv j-i\pmod 2\) and total length \(L-(j-i)+\ell\).

The Lean construction checks the sufficient direction for a replacement of unchanged length, including boundary blocks. The exact set criterion and variable-length version are written mathematical deductions; the native programs also check each accepted entire path independently.

## Why repeating short moves cannot help

Take the union of the saved bank's cube-isometry and reversal classes. The move rule is invariant under these symmetries. Complete enumeration from every representative shows that one allowed move stays in this union. Induction on the number of moves gives the same conclusion for any finite sequence. Both-endpoint nonextendibility is preserved by the same symmetries. Thus a finite sequence of these length-preserving moves cannot unlock a one-edge extension.

Lean checks the general finite-chain and nonextension implications with explicit closure and blocked-family hypotheses. The numerical closure premise for the 131 representatives remains native. This is not a classification of all 191-edge snakes and gives no global upper bound. A successful construction through this move family must use a block longer than 33 edges, or a different operation.

## Enumerations and completeness

The original 3--5-edge census first enumerates induced routes between each pair of endpoints and filters against the retained path. The longer search enumerates directly in the region freed by a deletion. At each step it rejects retained vertices, neighbours of retained non-anchors, repeats and chords to earlier replacement vertices. Distance and parity provide necessary pruning. Every legal next cube neighbour is considered; a target is accepted only at the specified depth. Canonical transition sequences use first-occurrence coordinate relabelling and the minimum of forward and reversed order. This is exact for translations, coordinate permutations and reversal, including unused coordinates.

The 6--24-edge sweep completed in 62.093 seconds. The 25--36 sweep stopped with status TIME_LIMIT after 180.015 seconds. Complete coverage ends at 33; any later completed seed rows and the current partial row are retained separately and do not establish full coverage of that longer block length. The earlier 3--5-edge census is retained unchanged.

## Shortening before endpoint growth

All replacements of a 4--24-edge block by a path shorter by two edges were enumerated. Their 189-edge outcomes form 231 symmetry classes. Complete endpoint growth, allowing either end at every step, finds no extension for 220 classes and exactly one extra edge at most for the other 11. No class can reach even 191 edges using endpoint additions alone. The computation does not exclude internal reroutings of these shorter paths before regrowth.

## Focusing the next search

Fix a candidate new endpoint \(w\) adjacent to an old endpoint. Every original nonattachment vertex equal or adjacent to \(w\) must be removed. If their smallest and largest indices are \(r,s\), a contiguous replacement from \(i\) to \(j\) must satisfy \(i<r\le s<j\), hence \(j-i\ge s-r+2\). An original blocking global endpoint would make the fixed-endpoint operation impossible. The current bank has no such endpoint blocker, and the recorded minimum necessary spans range from 2 to 190. These are only necessary conditions.

Lean checks that every old blocker lies in the changed interior under the actual agreement and separation premises, together with the span inequality. The next useful search is to impose these blocker requirements before enumerating larger replacements. This directly targets a 192-edge extension. Another open operation is to reroute a 189-edge shortened state before trying endpoint growth. Neither operation has been searched in this round.

## Verification and inherited state

Two new Lean modules pass, with five theorem dependency reports, no admitted statements and no native decision oracle. The unchanged guards require 1GiB free at startup, 768MiB reserve, at most 256MiB per Lean process, 60 seconds per check and one heavy research worker. One small census startup stopped below the threshold, then was retried after memory recovered. Generic proof checks do not certify native enumeration completeness.

The contributor branch was fetched at aeab10ecbab6480a11f927e590b664bd7f0b4f5f. Its report states 2639/3118 production modules and 746/748 replay migrations. The diff is archived; these additions were neither merged nor independently rebuilt. Archived 235, conditional 233/234, and pending graph-to-snake obligations retain their earlier qualifications. Full manuscript consistency review remains scheduled for round 200.
