from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
accepted={p.name.removesuffix('-audit.json') for p in (H/'data').glob('*-audit.json') if json.loads(p.read_bytes())['status']=='PASS'}
complete='EndpointTransport198' in accepted and all(f'PairRows198_{i}' in accepted for i in range(4)) and 'Cliques198' in accepted
parts=['The concrete triangle data and Boolean occupancy implication pass Lean.']
parts.append('The endpoint transport theorem passes Lean.' if 'EndpointTransport198' in accepted else 'The endpoint transport proof is prepared; its complete Lean check remains pending.')
parts.append('The complete concrete paired-path checks pass Lean.' if all(f'PairRows198_{i}' in accepted for i in range(4)) else 'The complete paired-path Lean checks remain pending; the native pairwise verification is complete.')
if 'Cliques198' in accepted:parts.append('The concrete triangle noncontainment theorem also passes Lean.')
parts.append('The exact three-orbit classification has the written proof above. Finite search outcomes remain native computations.')
verification=' '.join(parts)

addition=r"""
\subsection{Clique restrictions and three endpoint classes}
\label{sec:symmetry198}

Consider the one-contact symmetry from the preceding subsection:
$h$ exchanges coordinates 1 with 4 and 3 with 6, then translates by 126.
Let $G$ be the graph consisting of $Q_7$ and the additional edges
$x\leftrightarrow h(x)$. Its extension to $Q_8$ has minimum displacement
three, so there are no loops or double-lift restrictions.

\begin{proposition}
The graph $G$ contains exactly eight copies of $K_4$, with disjoint
vertex sets, and exactly 32 triangles. An induced path uses at most
two vertices of each of these cliques.
\end{proposition}
\begin{proof}
The displacement of $h$ is
\[
\Ham(x,h(x))=2+2\mathbf1_{x_1=x_4}+2\mathbf1_{x_3=x_6}.
\]
A triangle must use exactly one matching edge: ordinary cube edges
have no triangle, and two matching edges cannot meet. Its matching
endpoints must have Hamming distance two. This happens exactly when
$x_1\oplus x_4=x_3\oplus x_6=1$.
Fix these four coordinates and coordinate 0, and vary coordinates 2 and 5.
The resulting square receives both diagonals from $h$, giving a $K_4$.
There are eight choices, and every triangle arises in this way. Each
clique has four triangles. Any larger clique or another $K_4$ would
contain a triangle already confined to one of these groups. Finally,
three selected vertices in one group would form a triangle, which
cannot lie in an induced path.
\end{proof}

Coordinate 0 is unaffected by $h$. Thus $G$ is the Cartesian product
of one edge with a 64-vertex graph. Each clique is paired with its
translate by 1. At most one coordinate-0 edge in such a paired group
can belong to an induced path, since two force a four-cycle. This
restriction is already implied by the full square exclusions.

\begin{proposition}
The graph $G$ has exactly three vertex orbits under graph automorphisms,
with representatives 10, 2 and 0 and sizes 32, 64 and 32, respectively.
Every induced path in $G$ can be carried to one with first endpoint
among these three representatives.
\end{proposition}
\begin{proof}
Let $k$ count the equal-bit pairs among $(1,4)$ and $(3,6)$.
The triangle vertices have $k=0$. An edge changes $k$ by at most one,
and matching edges preserve it. Flipping one coordinate of each
equal-bit pair reaches a triangle vertex in exactly $k$ steps.
Hence $k$ is the distance from the triangle vertices and is invariant
under every graph automorphism.

Translations by 1, 4, 32, 18 and 72 commute with $h$, as does the
coordinate permutation $(1\ 3)(4\ 6)$. They therefore preserve $G$.
The paired translations alter the common orientations freely;
the fixed-coordinate translations alter the remaining bits. Exchanging
the pairs relates the two possibilities when exactly one pair agrees.
These operations are transitive on each of the three classes, whose
sizes and representatives follow directly. Mapping the first endpoint
of a path by the appropriate automorphism preserves its length and
inducedness.
\end{proof}
This permits three endpoint cases for an unrestricted search. A retained
seed condition must be transported as well; imposing the three roots
while leaving a fixed seed unchanged would not give a complete search.

An ordered extension search starts from the earlier 46-vertex direct
subpath in each orientation. With the first 18 vertices fixed, exhaustive
native searches visit 447,558 and 31,252 nodes and attain maxima 46 and
48 quotient vertices, respectively. These are exact maxima only for the
two specified prefix-extension families. Searches retaining 12 vertices
stop after about 35 seconds per orientation and yield no upper restriction.

The 48-vertex result uses only ordinary cube steps and gives two
separated 47-edge paths in $Q_8$. The first starts at 63 with transition
sequence
\[
\mathtt{42104260210430240530421043024056042153124012310}.
\]
The second starts at 137, with coordinates 1 and 4 and coordinates 3
and 6 exchanged in the transitions. The final vertices are 1 and 255.
Every pairwise path and separation condition passes a direct native check.
Their cross-distance counts at distances 0 through 8 are
\[
(0,0,160,390,576,658,388,104,28).
\]
This distribution differs from that of every one of the 36 face forests
saved in the earlier comparison. Distance preservation therefore proves
inequivalence to those forests; this does not classify all faces of all
known nine-dimensional snakes.

The connected quotient model with the eight clique restrictions remains
unresolved for 50 vertices and at most five omitted seed vertices after
90.047 seconds. The new 96-vertex paired face requires 97 compatible
opposite-face vertices to produce 192 edges. Its four-port completion
query remains unresolved after 120.047 seconds. Neither timeout is an
exclusion. No numerical bound changes.

VERIFICATION
Exact inputs, witnesses, restricted searches and proof receipts appear
in~\cite{symmetry198archive}. The next unrestricted construction search
can use the three endpoint cases. The simpler family avoiding all matching
steps may also be searched separately; in that family ordinary cube
parity balance is valid and $S\cap h(S)=\varnothing$ is required.

""".replace('VERIFICATION',verification)
p=D/'snake9_research.tex';s=p.read_text(encoding='utf-8');assert '\\label{sec:symmetry198}' not in s
anchor='\\section{Construction experiments and their scope}\\label{app:experiments}';assert s.count(anchor)==1;s=s.replace(anchor,addition+anchor)
bib=r"""\bibitem{symmetry198archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Clique restrictions and endpoint classes in a symmetry quotient}.
Research record 198, 13 November 2026. Concrete paired paths, exact structural data and verification receipts:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/198-symmetry-cliques}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}');p.write_text(s,encoding='utf-8',newline='\n')
p=D/'snake9_frontier_explanation.tex';s=p.read_text(encoding='utf-8');s=s.replace('Research state after round 197','Research state after round 198').replace('research records 175--197','research records 175--198')
a=s.index('\\paragraph{Using symmetry to organize the next construction.}');b=s.index('\\textbf{7. What is proved, and what remains.}',a)
front=r"""\paragraph{Using symmetry to organize the next construction.}
A cube involution is classified, up to cube conjugacy, by its coordinate
swaps and flipped fixed coordinates. Translation of the origin removes
flips on swapped pairs. The number of flipped fixed coordinates equals
the minimum distance between paired vertices. Choosing one such coordinate
gives $g(y,b)=(h(y),1-b)$, whose quotient is $Q_7$ with the additional
edges $y\leftrightarrow h(y)$. Three flipped fixed coordinates for $g$
eliminate partner edges and double-lift restrictions.

A free symmetry preserving one finite snake must reverse it: fixing an
endpoint fixes every vertex by path distance. Reversal forces either
a fixed middle vertex or adjacent exchanged middle vertices. Thus a
symmetry moving every vertex by at least two edges cannot preserve
one whole snake. It can exchange two components, with the final joining
paths breaking the symmetry.

The full census of 6512 affine involutions against one 50-edge $Q_7$
seed identified two one-contact placements. The chosen case exchanges
coordinates 1 with 4 and 3 with 6 and translates by 126. Its quotient
has eight disjoint $K_4$ groups, each allowing at most two path vertices.
Indeed, a triangle uses one matching edge of Hamming length two;
this requires the bits in each swapped pair to differ. Varying the
two flipped fixed coordinates then gives a square with both diagonals.

There are exactly three endpoint classes, represented by 10, 2 and 0.
They are distinguished by distances zero, one and two from the triangle
vertices. Paired translations, fixed-coordinate translations and exchange
of the two coordinate pairs act transitively within each class.
An unrestricted path search therefore needs only three fixed endpoints.
A retained seed must be transformed too if such a condition is imposed.

A connected extension search now produces two separated 47-edge $Q_8$
paths under this symmetry. Their cross-distance distribution differs
from all 36 saved comparison forests, providing a distinct candidate.
The paths use only ordinary $Q_7$ steps, so each remains in one
seven-dimensional face. Their 96 vertices need 97 compatible vertices
in the opposite face to produce a 192-edge snake. That completion
query remains unresolved after 120.047 seconds. The 50-vertex quotient
search with at most five seed omissions is also unresolved.

VERIFICATION
The next step uses the three endpoint cases or the simpler subfamily
avoiding matching steps. Any larger pair still needs a compatible
opposite-face completion. No longer snake or improved numerical bound
has been obtained.

""".replace('VERIFICATION',verification)
s=s[:a]+front+s[b:];p.write_text(s,encoding='utf-8',newline='\n')
records=[]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/name;q=R/'paper'/name;q.write_bytes(p.read_bytes());records.append(dict(editor=str(p),mirror=str(q),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(H/'data/document-mirrors.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8',newline='\n')
print('UPDATED_DOCUMENTS; complete new proof chain:',complete)
