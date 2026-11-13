from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
addition=r"""
\subsection{Symmetry classes and the paired-path construction}
\label{sec:symmetry197}

Permuting and joining copies of lower-dimensional paths is an established
construction method; Wynn uses both approaches in~\cite{wynn2012}.
The present calculation organizes the paired-path search by cube symmetries
and separates the choice of symmetry from the choice of path.

\begin{proposition}
Let $g(x)=\pi x\oplus a$ be an involution of $Q_n$. Up to conjugacy by
cube symmetries, it is determined by the number $r$ of transposed coordinate
pairs and the number $f$ of flipped fixed coordinates. Its minimum
Hamming displacement is $f$. The number of concrete maps of this type is
\[
\frac{n!}{r!f!(n-2r-f)!}.
\]
\end{proposition}
\begin{proof}
The involution conditions are $\pi^2=1$ and $\pi a=a$, so translation
bits agree on each transposed pair. Conjugation by translation $t$
replaces $a$ by $a\oplus t\oplus\pi t$. This removes the common bit
on each transposed pair and preserves the fixed-coordinate bits.
Coordinate relabelling then gives the stated classification. Conversely,
the permutation cycle type and the number of flipped fixed coordinates
are unchanged by these conjugations.
Every flipped fixed coordinate contributes one to displacement; the
transposed pairs can simultaneously contribute zero. For the count,
choose and pair the $2r$ moved coordinates, choose the $f$ flipped fixed
coordinates, and choose the common translation bit on each pair.
The last factor $2^r$ cancels the factor for unordered pairs.
\end{proof}

A fixed-point-free involution has $f\ge1$. Choose a flipped fixed
coordinate as the last coordinate to write it as
\[
g(y,b)=(h(y),1-b).
\]
Its orbit representatives lie in $b=0$. The quotient retains the ordinary
$Q_{n-1}$ edges and adds $y\leftrightarrow h(y)$. A fixed point of $h$
gives an orbit containing an edge and must be excluded. If $h(y)$ is
already an ordinary neighbour of $y$, both endpoints of that quotient
edge cannot be selected, since it has two distinct lifts. Subject to
these restrictions, an induced quotient path lifts to a separated pair
by the preceding lifting argument.

If $h$ has $r$ transposed pairs and $f$ flipped fixed coordinates, the
extended map $g$ has minimum displacement $f+1$. Thus $f\ge2$ removes
both obstructions above. For odd $f$, the quotient is bipartite under
ordinary cube parity. For even $f$, matching edges preserve parity,
so ordinary parity balance cannot be imposed on a quotient path.

\begin{proposition}
A fixed-point-free cube symmetry of minimum displacement at least two
cannot preserve the vertex set of a nonempty finite snake.
\end{proposition}
\begin{proof}
Its restriction would be an automorphism of the induced path. Fixing an
endpoint fixes every vertex by distance along the path. Therefore the
restriction reverses the path. An odd vertex count gives a fixed middle
vertex; an even count gives two adjacent middle vertices exchanged by
the symmetry. Both contradict the assumptions.
\end{proof}
The central contradiction under a reversal premise passes Lean. The
path-automorphism argument and general involution classification are
written proofs. This distinction motivates imposing symmetry on two
components while allowing the final joining paths to break it.

For the map used in Section~\ref{sec:cycles196}, conjugating by
translation 5 changes the translation mask from 63 to 34. Deleting
flipped coordinate 1 gives the seven-dimensional map that swaps
coordinates 0 with 2 and 1 with 3, then flips coordinate 4.
Lean checks the conjugacy, orbit labels, representative identities,
matching involution, and all $128\cdot8=1024$ neighbour identities.
The extra matching duplicates an ordinary edge precisely when bits
0 and 2 agree and bits 1 and 3 agree. Hence there are 32 incident
vertices and 16 forbidden pairs.

There are 20 types of affine involutions on $Q_7$, and their class sizes
sum to 6512. Extending them by the flipped eighth coordinate represents
all 20 free involution types in $Q_8$. A complete native enumeration
places each of the 6512 maps against the displayed 50-edge $Q_7$ snake.
For a contiguous subpath with vertex set $S$, the direct pair in the
two faces is separated exactly when $S\cap h(S)=\varnothing$.
The longest such subpath has 45 edges, yielding a 92-vertex paired
forest. This is below the saved 47-edge pairs from the other construction.
The enumeration concerns one fixed seed and its contiguous subpaths;
it does not classify arbitrary quotient paths or all optimal $Q_7$ snakes.

Exactly two placements have one contact on the full 51-vertex seed.
Their types for $h$ are $(1,1)$ and $(2,2)$, and their contacts occur
at zero-based positions $(38,43)$ and $(4,38)$, respectively.
The added edges close cycles of lengths 6 and 35. The second placement
extends to a $Q_8$ map of type $(2,3)$, with minimum displacement three
and no double-lift restrictions. Its quotient is nonbipartite.

For both one-contact cases, native solver calculations exclude a
50-vertex induced quotient path omitting at most four seed vertices,
with endpoints free. The times are 6.532 and 6.875 seconds, using
three cycle cuts and one cycle cut respectively. The five two-contact
placements of type $(2,1)$ are also excluded under the same restriction.
Thus each of these seven specific placements requires at least five
omitted seed vertices and at least four added vertices. The seed itself
has a quotient chord, so this statement concerns repair of a vertex set.
It must not be interpreted as a replacement between two valid quotient
snakes. The new solver contradictions and cycle sets are not certified
by the earlier Lean cycle checks.

For the one-contact type $(2,2)$, allowing eight omissions remains
unresolved: the 50-vertex query returns \texttt{UNKNOWN} after
120.016 seconds, and the 49-vertex query after 90.031 seconds.
No new lower or upper bound follows.
A useful next subdivision retains the contact $(4,38)$ as a path edge
and removes at least one ordinary neighbour of each endpoint, or omits
a contact endpoint and repairs the break. Keeping the original two
seed endpoints requires an odd number of matching steps. Maintaining
one ordered path during this search avoids disconnected cycles.
The resulting pair must still have compatible crossing ports and
opposite-face paths. The complete census, models and ten accepted
Lean modules are recorded in~\cite{symmetry197archive}.

"""
main=D/'snake9_research.tex';text=main.read_text(encoding='utf-8')
assert '\\label{sec:symmetry197}' not in text
anchor='\\section{Construction experiments and their scope}\\label{app:experiments}'
assert text.count(anchor)==1
text=text.replace(anchor,addition+anchor)
bib=r"""\bibitem{wynn2012}
E.~Wynn. \emph{Constructing circuit codes by permuting initial sequences}.
arXiv:1201.1647, 2012. \url{https://arxiv.org/abs/1201.1647}.

\bibitem{symmetry197archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Symmetry classes and quotient constructions}.
Research record 197, 13 November 2026. Complete placement census,
restricted repairs and checked quotient identities:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/197-symmetry-placement}.

"""
text=text.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
main.write_text(text,encoding='utf-8',newline='\n')
front=D/'snake9_frontier_explanation.tex';text=front.read_text(encoding='utf-8')
text=text.replace('Research state after round 196','Research state after round 197').replace('research records 175--196','research records 175--197')
paragraph=r"""
\paragraph{Using symmetry to organize the next construction.}
Write a cube involution as a coordinate permutation followed by bit
flips. Its permutation consists of transposed pairs and fixed coordinates.
Translation of the origin removes the flips on transposed pairs. Thus,
up to cube conjugacy, only the number of pairs and the number of flipped
fixed coordinates matter. The latter number is exactly the minimum
distance between paired vertices: every fixed flip contributes one,
while the transposed pairs can contribute zero.

Choosing one flipped fixed coordinate gives
$g(y,b)=(h(y),1-b)$. Its quotient is the ordinary $Q_7$ graph with the
additional matching $y\leftrightarrow h(y)$. A path in this quotient
lifts to two separated $Q_8$ paths when orbits containing partner
edges are omitted and the endpoints of a double-lift edge are never
both selected. Three flipped fixed coordinates for $g$ remove
both obstructions. Lean checks the earlier symmetry's concrete quotient,
including all 1024 neighbour identities.

Symmetry should act on the two components. A fixed-point-free symmetry
preserving a single finite path must reverse it, since fixing an endpoint
fixes every vertex by path distance. Reversal forces either a fixed
middle vertex or two adjacent exchanged middle vertices. Therefore a
symmetry moving every vertex by at least two edges cannot preserve
one whole snake. Lean checks the central contradiction under the
reversal premise; the preceding path-automorphism argument is written.

The census covers all 6512 affine involutions $h$ in 20 types, relative
to the displayed 50-edge $Q_7$ seed. Direct compatible subpaths reach
45 edges, giving two separated paths with 92 vertices. Two placements
have only one unwanted contact. Both require at least five omitted
seed vertices and four additions to reach 50 quotient vertices,
according to restricted solver exclusions. The seed has a quotient
chord and is not itself a valid quotient snake. The cleaner case has
contact $(4,38)$ and partner distance at least three. Searches with
eight omissions remain unresolved for both 50 and 49 quotient vertices.

The next step is to retain that contact as a deliberate path edge,
remove an ordinary neighbour at each end, and reconnect the remaining
chains; a second branch omits a contact endpoint. Endpoint compatibility
with the opposite-face forest must be retained. This provides a more
specific construction route without changing the numerical bounds.
The census and solver exclusions have not been certified in Lean.

"""
anchor='\\textbf{7. What is proved, and what remains.}'
assert text.count(anchor)==1
text=text.replace(anchor,paragraph+anchor)
front.write_text(text,encoding='utf-8',newline='\n')
records=[]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 original=D/name;mirror=R/'paper'/name;mirror.write_bytes(original.read_bytes())
 records.append(dict(editor=str(original),mirror=str(mirror),sha256=hashlib.sha256(original.read_bytes()).hexdigest()))
(H/'data/document-mirrors.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8',newline='\n')
print('UPDATED_EXISTING_DOCUMENTS',len(records))
