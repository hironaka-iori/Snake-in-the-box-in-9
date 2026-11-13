from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert json.loads((H/'data/IsometricPlacement199-audit.json').read_bytes())['status']=='PASS'
addition=r"""
\subsection{Relative placements without an involution restriction}
\label{sec:symmetry199}

The preceding quotient uses an involution to exchange two components.
A more general construction permits different parent shapes and any
relative cube isometry.

\begin{proposition}
Let $P,Q$ be induced paths in $Q_7$ with vertex sets $S,T$, and let
$f$ be a cube isometry. The copies $(P,0)$ and $(f(Q),1)$ are separated
induced paths in $Q_8$ if and only if
\[
S\cap f(T)=\varnothing.
\]
\end{proposition}
\begin{proof}
Within either face, the embedding and the isometry preserve distances,
so both paths remain induced. Across the two faces,
\[
\Ham((u,0),(f(v),1))=1+\Ham(u,f(v)).
\]
An edge between the paths therefore exists exactly when their projections
coincide. Distinctness across the faces is automatic.
\end{proof}
The proposition requires neither congruent parents nor $f^2=\mathrm{id}$.
It does not provide an involution quotient: the map
$(y,b)\mapsto(f(y),1-b)$ has square $(y,b)\mapsto(f^2(y),b)$.

For a fixed pair of parent sets, all relative placements can be counted
directly. Every cube isometry is $f(v)=\pi(v)\oplus t$, with $\pi$ a
coordinate permutation. For each of the $7!=5040$ permutations, compute
\[
c_\pi(t)=\#\{(u,v)\in S\times T:u\oplus\pi(v)=t\},
\qquad t\in Q_7.
\]
Because $\pi$ is bijective, each intersection vertex determines one
pair, giving $c_\pi(t)=|S\cap(\pi(T)\oplus t)|$. Thus a zero entry is
exactly a separated placement. There are $5040\cdot128=645120$ entries
for each parent pair.

Both parent paths may be normalized independently when all isometries
are included. Replacing them by $\alpha(S),\beta(T)$ changes the relative
map to $\alpha^{-1}f\beta$, which still ranges over the full family.
Reversing the ordered pair replaces $f$ by $f^{-1}$ and preserves the
intersection size, so unordered parent pairs suffice. Independent
normalization would generally be invalid for an involution-only family;
conjugation preserves that family when the same coordinate change is
applied on both sides.

Parents are deduplicated using transition words, relabelling coordinates
in their order of first appearance and allowing reversal. Equality of
these normalized words is equivalent to a cube isometry of the paths:
translation fixes the starting vertex, the coordinate correspondence
then fixes every step, and unused coordinates can be matched arbitrarily.
Conversely, an isometry between paths preserves their order or reverses it.

Extending the first 24 vertices of the published 51-vertex $Q_7$ parent
in both orientations exhausts three classes with 50 vertices and fourteen
classes with 49 vertices. The extension requires each new vertex to avoid
all earlier vertices and their neighbourhoods except the current endpoint.
This covers exactly the extensions of those two prefixes. Searches from
16-vertex prefixes stop at 3,000,001 visited nodes each and add no new class;
they do not exhaust the larger families.

\begin{center}
\begin{tabular}{lrrl}
\toprule
Parent sizes & Pairs & Placements per pair & Minimum intersection\\
\midrule
51 and 51 & 1 & 645120 & 2\\
50 and 50 & 6 & 645120 & 2 in every case\\
51 and 49 & 14 & 645120 & 2 in twelve cases; 3 in two\\
\bottomrule
\end{tabular}
\end{center}
The first row uses the published parent twice. The second uses all
unordered pairs, including self-pairs, of the three saved classes.
The third pairs the published parent with each saved 49-vertex class.
These complete native calculations exclude a separated 100-vertex face
for the latter two saved families. They do not classify all $Q_7$ paths.
The numerical censuses have no proof-assistant replay; the general
path-image, separation and representative-change deductions pass Lean.
Exact inputs, coverage counts and intersection histograms are retained
in research record~\cite{research199}.

The three unrestricted quotient cases with first endpoint 10, 2 or 0
each remain unresolved after a 45-second search. An alternative fixes
the published 51-vertex parent and allows any 49-vertex induced path
in its complement, a graph with 77 vertices and 141 edges. A connected
circuit query with no symmetry or seed-overlap restriction remains
unresolved after 60 seconds. None of these time limits excludes a path.

A successful complement construction would give 100 vertices in the
paired $Q_8$ face. A four-crossing $Q_9$ completion still needs 93,
95 or 97 opposite-face vertices for 192, 194 or 196 edges, respectively.
Changing only the relative symmetry cannot improve the completely
scanned parent pairs. Further progress requires other parent shapes,
paths using matching steps in the quotient, or a different face
arrangement. No new $Q_9$ witness or global bound follows from this round.

"""
p=D/'snake9_research.tex';s=p.read_text(encoding='utf-8');assert '\\label{sec:symmetry199}' not in s
settings=s[:s.index('\\begin{document}')]
marker='\\section{Construction experiments and their scope}\\label{app:experiments}'
assert s.count(marker)==1;s=s.replace(marker,addition+marker)
bib=r"""
\bibitem{research199}
I. Hironaka, T. Ma and S. Zhan,
\emph{Relative symmetry placements and parent diversity},
research record 199, 13 November 2026. Complete finite placement data,
general separation deductions and verification receipts:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/199-parent-diversity}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}');assert s[:s.index('\\begin{document}')]==settings
p.write_text(s,encoding='utf-8',newline='\n')
p=D/'snake9_frontier_explanation.tex';s=p.read_text(encoding='utf-8');s=s.replace('Research state after round 198','Research state after round 199').replace('research records 175--198','research records 175--199')
a=s.index('\\paragraph{Using symmetry to organize the next construction.}');b=s.index('\\textbf{7. What is proved, and what remains.}',a)
front=r"""\paragraph{Using symmetry to organize the next construction.}
The involution quotient from the preceding work has three endpoint
classes, represented by 10, 2 and 0. They are distances zero, one and
two from its triangle vertices. Cube symmetries act transitively in
each class, so three unrestricted endpoint cases cover every quotient
path. The corresponding 50-vertex searches remain unresolved after
45 seconds per case. This is a time limit, without an exclusion.

The checked pair of separated 47-edge $Q_8$ paths remains available.
Its 96 vertices require 97 compatible opposite-face vertices for a
192-edge $Q_9$ snake. That completion remains unresolved.

A broader use of symmetry allows any cube isometry and different
parent shapes. Let $S,T$ be the vertex sets of two induced $Q_7$ paths.
The copies $(S,0)$ and $(f(T),1)$ in $Q_8$ are separated exactly when
\[
S\cap f(T)=\varnothing.
\]
Within each face the paths remain induced. Across faces the Hamming
distance is one plus the distance of the projections, so an unwanted
edge is exactly a coincident projection. No involution condition is
needed for this construction. Involution quotients remain a separate
method, since applying $(y,b)\mapsto(f(y),1-b)$ twice gives $f^2(y)$.

For a fixed parent pair, every possible placement is obtained by
5040 coordinate permutations and 128 translations. For each permutation
$\pi$, counting pairs with $u\oplus\pi(v)=t$ gives exactly the
intersection size at translation $t$. Scanning all 645120 entries
therefore decides disjoint placement for that pair. Normalizing either
parent and reversing their order only changes which isometry is scanned.

Extensions of two fixed 24-vertex prefixes of the published parent
give three classes with 50 vertices and fourteen with 49 vertices.
Every placement of any pair from the three 50-vertex classes overlaps
in at least two vertices. Pairing the published 51-vertex parent with
the fourteen 49-vertex parents also always overlaps: the minimum is
two in twelve cases and three in the remaining two. Consequently,
changing relative symmetry alone cannot produce a 100-vertex paired
face from these saved families. The calculation does not cover all
possible parent shapes.

The generic path-image, layer-separation and representative-change
arguments pass Lean, with five theorem reports. The complete numerical
censuses remain native computations, without a Lean replay.

The next broader query seeks any 49-vertex induced path in the
complement of the published 51-vertex parent. This allowed graph has
77 vertices and 141 edges; the query remains unresolved after 60 seconds.
It imposes no symmetry or shape condition on the second parent.
A witness would give a 100-vertex paired face, still needing 93,
95 or 97 compatible opposite-face vertices for 192, 194 or 196 edges.
Further work must change the parent shapes or the face arrangement,
or use matching steps in the earlier quotient. No longer snake or
improved global numerical bound has been obtained.

"""
s=s[:a]+front+s[b:];p.write_text(s,encoding='utf-8',newline='\n')
records=[]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/name;q=R/'paper'/name;q.write_bytes(p.read_bytes());records.append(dict(editor=str(p),mirror=str(q),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(H/'data/document-mirrors.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8',newline='\n')
print('UPDATED_EXISTING_EDITOR_DOCUMENTS_AND_MIRRORS')
