"""Add the proved subset deduction to the existing editor documents."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/name;before=H/'data'/('before-'+name)
 if not before.exists():before.write_bytes(p.read_bytes())
main=(H/'data/before-snake9_research.tex').read_text(encoding='utf-8')
addition=r'''
\subsection{Subset capacity within the square-base family}
\label{sec:subset211}
The saturated family contains 32 intervals whose free words must be
pairwise distinct. Its joint domain restrictions can therefore be stronger
than separate binary supports. This is an application of standard matching
methods for distinct-value constraints~\cite{regin1994}; no novelty of the
general filtering principle is claimed.

\begin{proposition}[Subset capacity and reserved words]\label{prop:subset211}
Let $I$ be a finite family of variables whose assigned words must be
pairwise distinct. For $i\in I$, let $D_i$ be its finite allowed-word set.
For $J\subseteq I$, put $U=\bigcup_{j\in J}D_j$.
Every satisfying assignment requires $|U|\ge|J|$.
If $|U|=|J|$, deleting $U$ from each $D_i$ with $i\in I\setminus J$
preserves every satisfying assignment.
\end{proposition}
\begin{proof}
The assigned words inject $J$ into $U$, proving the inequality.
In the equality case, their image is all of $U$. Every other variable
in $I$ must differ from each of those words and therefore lies outside
$U$. The same complete assignment survives each deletion, so every
other constraint on it remains satisfied.
\end{proof}
The equality conclusion also applies to a variable outside $I$ if
it is proved unequal to every member of $J$. It cannot be applied to
the nine outside singleton intervals merely because they are outside
the chosen family: their allowed antipodal sharing must be retained.
Four Lean deductions check saturation, outside-word exclusion,
preservation of the same assignment after domain filtering, and the
deficient-pool contradiction. These checks retain explicit distinctness,
domain-containment and conflict premises~\cite{research211}.

\paragraph{Finding the subsets.}
A matching assigns a different allowed word to each of the 32 variables.
When a matching is found, direct an arc from a variable to the owner of
every word in its domain. Every reachable set is closed under these arcs.
Its domain union is therefore precisely the matched words of its members,
and has the same cardinality. Such a set supplies the equality case of
Proposition~\ref{prop:subset211}. Failed augmentation can instead supply
a deficient subset. The implementation recomputes the actual union and
cardinality before every rejection or deletion. Matching serves to find
the subsets; the explicit counting condition justifies the deductions.
Only other members of the distinct-word family are pruned.

The seven unfinished regions for retained coordinates $(0,5)$ were
transferred with all domain vectors, their order and the original binary
model unchanged. The new engine retains the previous branching and
saved-coverage procedure. Its source and transfer have independent
reviews, while the concrete masks, matching discovery and entire native
traversal remain outside the Lean proof. Search totals at the round-211
cutoff are recorded below. No speed improvement is inferred from raw
pruning counters, and no completed global bound follows.
% ROUND211_SEARCH_STATUS

'''
anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}'
if main.count(anchor)!=1:raise RuntimeError('Main insertion anchor')
main=main.replace(anchor,addition+anchor,1)
bib=r'''\bibitem{regin1994}
J.-C.~R\'egin. \emph{A filtering algorithm for constraints of difference
in CSPs}. Proceedings of AAAI-94, pp.~362--367, 1994.
\url{https://cdn.aaai.org/AAAI/1994/AAAI94-055.pdf}.

\bibitem{research211}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Subset capacity in the
six-coordinate history search}. Research record 211, November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/211-subset-capacity}.

'''
main=main.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
front=(H/'data/before-snake9_frontier_explanation.tex').read_text(encoding='utf-8')
front=front.replace('Research state after round 210','Research state after round 211')
start=front.index('The strengthened $(0,5)$ search is open after')
end=front.index(r'\paragraph{Why continuation',start)
front=front[:start]+r'''\paragraph{Subset capacity.}
For any set $J$ of intervals required to have distinct words, let $D_j$
be the current allowed words and $U=\bigcup_{j\in J}D_j$. Then
\[
|U|\ge |J|.
\]
If equality holds, every word of $U$ is assigned within $J$. Therefore
those words can be removed from every other interval in the same
distinct-word family. The reason is finite counting: an injection
between equally sized finite sets uses the entire target set.
The nine outside singleton intervals can share partner words, so
this removal must not be applied to them without further conflicts.

Four Lean deductions check these implications and preservation of
every complete assignment. A separate native engine uses matching
to find subsets and checks their explicit union sizes before pruning.
All seven unfinished regions were transferred unchanged from round 209.
The matching implementation and complete traversal retain native status;
the generic Lean result does not certify a whole-model exclusion.
% ROUND211_SEARCH_STATUS
No controlled comparison establishes a speed improvement.

'''+front[end:]
front=front.replace('milestones through round 210','milestones through round 211')
for name,s in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
 (D/name).write_text(s,encoding='utf-8',newline='\n')
 (R/'paper'/name).write_bytes((D/name).read_bytes())
print('Updated existing documents with subset proof and explicit scope.')
