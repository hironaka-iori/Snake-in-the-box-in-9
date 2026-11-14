"""Update the existing manuscripts with the spare-capacity argument."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert not (H/'data/history-search.lock').exists()
for module in ['SpareSupport212','SupportBridge212','PartnerSubset212']:
    assert json.loads((H/'data'/(module+'-audit.json')).read_bytes())['status']=='PASS'
state=json.loads((H/'data/case-22/state.json').read_bytes())
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    before=H/'data'/('before-'+name)
    assert not before.exists()
    before.write_bytes((D/name).read_bytes())
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
front=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
addition=r'''
\subsection{Using the remaining capacity to restrict partner sharing}
\label{sec:spare212}
The previous inequality bounds the number of outside intervals whose
words are absent from the chosen family. It also gives a restriction
on their current domains, even when the chosen family is unsaturated.

\begin{proposition}[Spare capacity and partner support]\label{prop:spare212}
Let $C$ and $O$ be disjoint families of variables taking words from an
alphabet of size $q$. Values are pairwise distinct within each family.
For $x\in O$, let $A_x\subseteq C$ contain every member of $C$ that
can share a value with $x$. Write $D_x$ for the current domain and put
\[
s=q-|C|,\qquad P_x=\bigcup_{y\in A_x}D_y,\qquad
F=\{x\in O:D_x\cap P_x=\varnothing\}.
\]
Every satisfying assignment requires $|F|\le s$. If $|F|=s$, replacing
$D_x$ by $D_x\cap P_x$ for each $x\in O\setminus F$ preserves every
satisfying assignment.
\end{proposition}
\begin{proof}
The chosen family uses $|C|$ different words. At most $s$ words of the
alphabet remain unused by it. Since outside values are also distinct,
at most $s$ outside variables can use these remaining words. Every
member of $F$ must do so: sharing with a listed partner is excluded by
its domain, and sharing with any other member of $C$ is excluded by
the partner hypothesis. This proves the bound. If $|F|=s$, these
variables exhaust the allowance. Every other outside variable must
share with a member of $C$, necessarily a listed partner. Its actual
word therefore belongs to $P_x$. The same complete assignment
survives all stated domain restrictions.
\end{proof}

The two parity families for retained coordinates $(0,6)$ have
$(|C|,|O|,s)=(30,9,2)$ and $(26,13,6)$, respectively.
The restrictions therefore activate after two even outside variables,
or six odd outside variables, are forced to avoid sharing.
The forced variables retain their unshared options.
Before the allowance is exhausted, this argument alone gives no
support restriction on another individual outside variable.

Lean checks the exception-counting deduction and its composition with
assigned values, partner completeness and domain containment. The
exception list and the implication from missing support are derived
in that composition. The geometric hypotheses, native domain masks
and complete search traversal retain their separate verification
obligations~\cite{research212}.

\paragraph{A stronger necessary condition for groups of outside variables.}
For $J\subseteq O$, let $N(J)$ contain the $y\in C$ for which some
$x\in J$ has $y\in A_x$ and $D_x\cap D_y\ne\varnothing$. Then
\begin{equation}\label{eq:partner-capacity212}
|J|\le |N(J)|+s.
\end{equation}
Indeed, each member of $J$ that shares a chosen-family word determines
a partner in $N(J)$. Distinct outside words give distinct partners.
The remaining members number at most $s$. This proves the inequality.
The earlier rejection rule is its special case $J=F$, for which
$N(J)$ is empty. The general inequality also detects competition for
too few partners when every individual outside variable has support.
Its generic finite counting argument is checked separately in Lean;
it is not integrated into the native search in this round.

\paragraph{Finite search and evidence boundary.}
The new search starts from the complete unchanged case retaining
$(0,6)$. It preserves all 78 root domains, the binary relations,
excluded source-isometric assignments and symmetry normalization.
The two added support families are consequences of 41,312 inspected
equal-word exclusions in the original tables. The input and root
preservation have an independent audit. This is a fresh complete-root
run; the earlier nonresumable limited search supplies no inherited
coverage. The current engine applies Proposition~\ref{prop:spare212}.
% ROUND212_SEARCH_STATUS
No controlled comparison establishes a speed improvement. An open
model gives no exclusion, and neither the restricted search nor its
generic counting lemmas determine the optimum in $Q_9$.

'''
assert main.count(r'\section{Verification scope and remaining problem}\label{sec:verification}')==1
main=main.replace(r'\section{Verification scope and remaining problem}\label{sec:verification}',addition+r'\section{Verification scope and remaining problem}\label{sec:verification}',1)
main=main.replace('The corresponding\nunsaturated-family search rules are not implemented in this round.','The round-211 counts alone do not identify which outside intervals\nshare. Section~\\ref{sec:spare212} develops their domain consequences.')
status=f'At the round-212 cutoff, the model remains open after {state["committed_jobs"]} saved\nsteps and {state["nodes"]:,} nodes, with {len(state["frontier"])} unfinished regions.\nThe other saved cases are unchanged, and 27 six-coordinate choices\nremain unresolved~\\cite{{research212}}.\n'
main=main.replace('% ROUND212_SEARCH_STATUS',status)
bib=r'''\bibitem{research212}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Spare capacity and partner support
in whole-coordinate history searches}. Research record 212, November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/212-spare-support}.

'''
main=main.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
front=front.replace('Research state after round 211','Research state after round 212').replace('milestones through round 211','milestones through round 212')
front=front.replace('Three have saved unfinished searches:\n$(0,4)$, $(3,4)$ and $(0,5)$; the remaining 24 have only initial limited\nruns.','Four have saved unfinished searches:\n$(0,4)$, $(3,4)$, $(0,5)$ and $(0,6)$; the remaining 23 have only initial\nlimited runs.')
front=front.replace('The other 26 unresolved\nsix-coordinate cases were unchanged in this round.','The round-212 search below addresses $(0,6)$; the remaining saved\ncases are unchanged.')
old='''Lean checks the counting implications and the literal source counts.
The complete geometric assembly remains a written proof. These
unsaturated-family constraints are a next search direction; their
implementation is still pending.'''
new=r'''\paragraph{When the spare allowance is exhausted.}
For an outside interval $x$, take the union $P_x$ of its allowed
partners' current domains. If $D_x\cap P_x=\varnothing$, its value must
be absent from the chosen family. Distinct outside values consume
different unused words. Thus there can be at most two such even
intervals or six such odd intervals for $(0,6)$.

Once this allowance is reached, every other outside interval must
share; intersecting its domain with $P_x$ preserves every solution.
The forced unshared intervals keep their options. Lean checks the
counting argument and the link from partner domains to actual
exceptions under explicit distinctness and partner hypotheses.
The complete geometric assembly and native traversal remain separate.

More generally, for a set $J$ of outside intervals let $N(J)$ contain
the chosen-family intervals that are listed partners of a member of
$J$ and have an intersecting current domain. With spare allowance $s$,
\[
|J|\le |N(J)|+s.
\]
Shared members inject into distinct partners; at most $s$ members
remain unshared. This generic counting consequence is also checked in
Lean. Its group rule is a possible stronger search step; only the
zero-support and exhausted-allowance rules are implemented here.
'''+ '\n'+status.replace(r'~\cite{research212}','')
assert front.count(old)==1
front=front.replace(old,new,1)
for name,content in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
    (D/name).write_text(content,encoding='utf-8',newline='\n')
    (R/'paper'/name).write_bytes((D/name).read_bytes())
print('UPDATED_EXISTING_DOCUMENTS')
