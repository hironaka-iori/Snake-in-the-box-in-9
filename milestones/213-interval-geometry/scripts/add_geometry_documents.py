"""Add the checked indexed-path restriction to the current manuscript sources."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
for module in ['IntervalGeometry213','ConcreteData213','ConcreteRelations213','ConcreteCoverage213','ConcreteGeometry213','ConcreteSupport213']:
    assert json.loads((H/'data'/(module+'-audit.json')).read_bytes())['status']=='PASS'
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
front=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
assert r'\label{sec:interval213}' not in main
addition=r'''
\subsection{Deriving partner restrictions from the indexed path}
\label{sec:interval213}
The capacity argument requires distinct chosen values, distinct outside
values and complete partner lists. These restrictions follow directly
from the path condition for the saved retained-coordinate construction.
Write each vertex as $(z_i,u_{g(i)})$, where $z_i\in Q_2$ and $g(i)$
identifies its constant-free-word interval. At consecutive indices,
the identifier stays unchanged or increases by one.

\begin{proposition}[Shared words across coordinate intervals]\label{prop:interval213}
Suppose $(z_i,u_{g(i)})$ is an induced path. If two different group
identifiers have the same parity and carry the same free word, every
base vertex of one group is opposite every base vertex of the other.
Each sharing group contains only one original path index. Three
different groups of that parity cannot carry a common free word.
\end{proposition}
\begin{proof}
Representatives of different groups with equal identifier parity cannot
be consecutive: a change at consecutive indices increases the identifier
by one and changes its parity. Their full vertices therefore have Hamming
distance at least two. Equal free words contribute zero distance, so the
two-coordinate bases must be opposite.

Fix a representative of the second group. Every representative of the
first is at its unique opposite corner and carries the same free word.
Two such indices would repeat a full vertex, contrary to injectivity.
The same reasoning applies to the second group. With three sharing
groups, being opposite twice makes the first and third bases equal.
Their free words are also equal, again repeating a full vertex.
\end{proof}

This argument has passed Lean directly from the indexed induced-path
condition, including either ordering of the representative indices.
For retained coordinates $(0,6)$, the grouping recurrence is checked
against the literal 99-vertex source. Every required chosen-family,
outside-family and nonpartner inequality has original-index witnesses
whose base corners are not opposite. The complete witness coverage
and validity are checked in bounded pieces and then assembled.
Applying Proposition~\ref{prop:interval213} derives distinctness and
partner completeness for both parity families~\cite{research213}.

Thus the source-specific support argument no longer assumes those
geometric restrictions separately from the reconstructed path.
Alphabet membership, current domain containment, coordinate
normalization and the complete native search certificate remain separate.
Decoding an arbitrary natural number into six bits alone does not prove
membership in the intended parity alphabet. The saved search states and
construction lower bound are unchanged in this round.

'''
anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}'
assert main.count(anchor)==1;main=main.replace(anchor,addition+anchor,1)
bib=r'''\bibitem{research213}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Indexed-path geometry and
source-specific partner restrictions}. Research record 213, November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/213-interval-geometry}.

'''
main=main.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
addition=r'''
\paragraph{Why the partner restrictions follow from a path.}
Different interval identifiers of the same parity cannot occur at
consecutive indices, because an identifier changes by at most one per
step. If their free words agree, the path condition forces their base
corners to be opposite. Fixing one opposite corner fixes the entire
other vertex, so injectivity permits only one index in either sharing
interval. Three sharing intervals would repeat a full vertex.

Lean now checks this argument from the indexed-path definition.
For the saved $(0,6)$ model, checked original-index witnesses also
derive distinctness within the chosen and outside families and the
completeness of their partner lists. Thus these restrictions are
connected to the actual reconstructed path. Alphabet membership,
current domains and the complete native search certificate remain
separate. No construction search state changes in this round.

'''
anchor=r'\section{What would resolve the question}'
assert front.count(anchor)==1;front=front.replace(anchor,addition+anchor,1)
front=front.replace('milestones through round 212','milestones through round 213')
for name,s in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
    (D/name).write_text(s,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes((D/name).read_bytes())
print('ADDED_CHECKED_GEOMETRY')
