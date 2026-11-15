"""Add round230 conclusions to the reviewed existing manuscripts in place."""
from pathlib import Path
import re
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):
    assert s.count(a)==1,a[:90]
    return s.replace(a,b,1)
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
main=once(main,'Research state after round 229, 15 November 2026','Research state after round 230, 16 November 2026')
main=once(main,'Native searches also exclude specified two-block\nconstruction families, with the crossing restrictions and unresolved\ncases stated explicitly.','Native searches exclude the specified two-block construction through\n46-edge replacements for every crossing count. A necessary face-visit\ninequality strengthens the last queries; its combinatorial proof and\nthe scope of its checked components are stated separately.')
main=once(main,r'Sections~\ref{sec:replacement225}--\ref{sec:projection229} give the',r'Sections~\ref{sec:replacement225}--\ref{sec:facevisits230} give the')
main=once(main,'intervals and crossing conditions.','intervals and length-preservation conditions. The latest cover permits\nevery crossing count.')
main=once(main,'The search with unrestricted crossing count excludes 304 of the\n315 maximal contexts and leaves 11 unresolved.','At the round-229 cutoff, the search with unrestricted crossing count\nexcluded 304 of the 315 maximal contexts and left 11 unresolved.\nSection~\\ref{sec:facevisits230} subsequently excludes all eleven.')
main=once(main,'These give the next lower-dimensional construction targets. They supply\nno witness, and counts of eight or more remain possible in the unresolved\nfamily.','These were the next lower-dimensional construction targets. At that\ncutoff they supplied no witness, and counts of eight or more remained\npossible in the unresolved family.')
addition=r"""\subsection{Face visits and completion of the two-block family}
\label{sec:facevisits230}
The eleven residual contexts of Section~\ref{sec:projection229} allow a
particularly small two-crossing reduction. Four have two retained
crossings and hence allocation $(0,0)$ between the replacements; seven
have one retained crossing and allocation $(1,0)$. Complete enumeration
of their upper pieces leaves fifteen pairs of lower-dimensional path
problems. Each native query is infeasible. The reduction uses only actual
joining projections as exemptions and imposes no boundary-change
condition. Combined with the 304 prior unrestricted exclusions, it
excludes two crossings throughout the same 315-context family.

The following necessary condition treats arbitrary crossing counts.
It applies to every coordinate and in every dimension.

\begin{proposition}[Face-visit inequality]\label{prop:facevisits230}
Let a nontrivial induced path in $Q_n$ cross a chosen coordinate $c$
times. Let $u$ and $l$ be its numbers of vertices in the two coordinate
faces, and let $r\in\{0,1,2\}$ be its number of endpoints in the first
face. Then
\begin{equation}\label{eq:facevisits230}
3c\le 2u+r,\qquad 3c\le 2l+2-r.
\end{equation}
In particular, a path of $m$ edges satisfies $3c\le m+2$.
\end{proposition}
\begin{proof}
For $c=0$ both inequalities are immediate. Suppose $c>0$, and partition
the path into maximal consecutive visits to the two faces. The visits
containing the endpoints are distinct. Every other visit contains at
least three vertices: a single-vertex visit would have the same vertex
immediately before and after its two crossing edges, and a two-vertex
visit would have adjacent flanking vertices at nonconsecutive path
positions. These violate injectivity and inducedness, respectively.

If there are $k$ visits to the first face, exactly $r$ meet an endpoint.
Each other visit meets two crossing edges and each endpoint visit meets
one. Hence $c=2k-r$. Since internal visits contain at least three
vertices and endpoint visits contain at least one,
\[
u\ge 3(k-r)+r=3k-2r.
\]
Thus $2u+r\ge 6k-3r=3c$. The other face has $2-r$ endpoint visits,
giving the second inequality. Adding them and using $u+l=m+1$ gives
$6c\le2m+4$, as required.
\end{proof}

Lean checked the internal-visit obstruction for actual compatible
induced pieces, a finite-list version of the vertex count, and its
conversion to the crossing inequality under explicit incidence and
endpoint-count identities. Extracting maximal visits and proving those
identities from a whole path remains the written argument above. The
general checked components do not certify numerical search exclusions.

Both endpoints of every complete candidate in the selected family lie
in the same face, so the total crossing count is even. Each of the eleven
residual contexts retains at least one crossing, excluding zero. The
completed same-context exclusions for two, four and six therefore imply
at least eight crossings. A final native query imposes this minimum and
\eqref{eq:facevisits230} on both replacement paths, without fixing an
exact crossing count or adding a boundary-change restriction. Each
replacement has 46 edges, so the proposition also gives $c\le16$ for
that replacement. Every actual candidate satisfies these conditions.

All eleven final queries are infeasible. Together with the earlier
106 geometric and 198 native exclusions, they cover all 315 maximal
contexts. Padding shorter replacements with their unchanged seed
vertices transfers the result to blocks of at most 46 edges. The
conclusion concerns the normalized bank123 seed, the appended endpoint
24, two separated length-preserving replacements, and retained anchors
and outside positions. It covers every crossing count within these
restrictions. Native finite enumeration, data extraction and solver
contradictions remain separate from the checked general lemmas. No
longer snake or global upper bound follows~\cite{research230}.

Continuing the construction search requires a change of scope. Comparing
extension endpoints and the positions of their conflicting retained
vertices across inequivalent seeds is a concrete next preparation.
Fewer or more closely placed conflicts may reduce the amount of retained
structure that must change. This is a research hypothesis; no such new
seed survey was carried out in this round. Wider or length-changing
replacements remain possible alternatives.

"""
main=once(main,r'\section{A numerical conjecture and its limitations}',addition+r'\section{A numerical conjecture and its limitations}')
main=once(main,'The computational exclusions retain their stated native dependencies.\nFull-source reviews',r'''The computational exclusions retain their stated native dependencies.
Section~\ref{sec:facevisits230} completes the two-crossing reduction and
the unrestricted width-46 family. Three general face-visit components
passed Lean; whole-path run extraction, finite coverage and numerical
contradictions retain the explicit limits stated there.
Full-source reviews''')
short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
short=once(short,'Research state after round 229','Research state after round 230')
start=short.index('The search with unrestricted crossing count excludes 304')
end=short.index(r'\section{Remaining questions}',start)
short=short[:start]+r'''At the end of round 229, the search with unrestricted crossing count
excluded 304 of the 315 maximal contexts. All nine earlier six-crossing
unknowns were excluded by broader queries that had imposed no six-count
restriction on those nine. The exact-six family was therefore covered
without circular reasoning~\cite{research229}.

In the eleven residual contexts, two total crossings force replacement
allocations $(0,0)$ in four cases and $(1,0)$ in seven. Enumerating the
short upper pieces gives fifteen pairs of paths to find in $Q_8$.
All fifteen native queries are infeasible. This excludes two crossings
throughout the selected family.

\section{Why repeated face visits require space}
Split a snake at every crossing of one chosen coordinate. Each remaining
piece is a consecutive visit to one of the two faces. An internal visit
has a crossing before and after it. It needs at least three vertices:
with one vertex, the two flanking vertices would coincide; with two,
the flanking vertices would be adjacent at nonconsecutive positions.
Both violate the snake condition.

Suppose there are $c>0$ crossings, $u$ vertices in the upper face and
$r$ endpoints there. If the path makes $k$ upper visits, exactly $r$
are endpoint visits. Counting their incident crossings and vertices gives
\[
c=2k-r,\qquad u\ge3(k-r)+r.
\]
Eliminating $k$, and then repeating the argument for the lower face, gives
\[
\boxed{3c\le2u+r,\qquad 3c\le2l+2-r.}
\]
Here $l$ counts lower vertices. The inequalities are immediate when
$c=0$. For a path of $m$ edges, adding them gives $3c\le m+2$.
A 46-edge replacement therefore crosses any chosen coordinate at most
16 times. Lean checked the local obstruction and the finite counting
implications. Extracting the visits from an arbitrary whole path remains
a written proof.

Every full candidate in the eleven residual cases has endpoints in the
same face and retains a crossing. Its total crossing count is therefore
positive and even. Since two, four and six are excluded, it must have at
least eight. The last search adds this requirement and the face-visit
inequalities while allowing every remaining crossing count.
All eleven queries are infeasible. Together with the earlier results,
this excludes all 315 maximal contexts and, by padding, every shorter
replacement in the same two-block family. This remains a native
computational exclusion with explicit seed, endpoint, anchor and
length-preservation restrictions~\cite{research230}.

'''+short[end:]
short=once(short,'The four-crossing two-block search excludes widths through 46 for the\nchosen endpoint and seed. The unrestricted-crossing search has the scope\nand remaining cases stated above. Wider blocks, different seeds or\nendpoints, and changed block lengths remain construction choices.','The selected two-block family is excluded through width 46 for every\ncrossing count. A new construction search must change a restriction.\nA useful next preparation is to compare extension endpoints across\ninequivalent seeds and count the retained vertices that conflict with\neach extension. Fewer or more closely placed conflicts may require less\nstructure to change; this expectation is unproved. Wider blocks and\nchanged block lengths remain construction choices.')
short=once(short,'milestones through round 229','milestones through round 230')
bib=r'''\bibitem{research230}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Face visits and completion of the
two-block construction exclusion}. Research milestone 230,
16 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/230-two-crossing-frontier}.

'''
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
    text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}')
    p=D/name;before=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',text).group()
    if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',text,re.S).group()
    p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes())
    print('UPDATED',name)
note=H/'logs/face-visits-proof.md';s=note.read_text(encoding='utf-8')
s=s.replace('`FaceVisits230.lean` is prepared source, with three intended axiom reports. It has not been compiled. No solver or tests were run. The only imported research dependency is the accepted `LayerJoining` source.','`FaceVisits230.lean` passed the guarded Lean compiler with three standard-axiom reports. The final accepted source hash is d3a99a456f7015a30feade83d9938e80cefd0c2a26ee57de017452b2e8f493c0. Two earlier elaboration failures are retained separately; only data/FaceVisits230-audit.json records the accepted attempt. The only imported research dependency is the accepted `LayerJoining` source. The proof author ran no solver or software tests.')
s=s.replace('The first proposed Lean theorem','The first accepted Lean theorem').replace('## Proposed checked components and remaining bridge','## Checked components and remaining bridge')
note.write_text(s,encoding='utf-8',newline='\n')
