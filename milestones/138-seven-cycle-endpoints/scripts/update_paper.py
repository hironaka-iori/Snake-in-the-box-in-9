"""Targeted paper update after completion of the actual-snake proof."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
state=json.loads((H/'data/proof-completion.json').read_text())
assert state['status']=='PASS_ACTUAL_NINE_TRANSITION_EXCLUSION_AND_CONDITIONAL_ARITHMETIC' and len(state['modules'])==16
receipt=json.loads((H/'data/ActualBase138Minimal-audit.json').read_text())
assert receipt['status']=='PASS' and receipt['exit_code']==0
assert any(a['theorem']=='Snake9.LocalWindow.CycleBase138.actual_cycle_row' for a in receipt['axioms'])
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');repo=R/'paper/snake9_research.tex'
old=editor.read_bytes();assert old==repo.read_bytes()
assert sha(old)=='8d98ae0a58e9e1748fe73bc78ca1786ee05415490a4cef7f6087228f24d885ad'
backup=H/'audit/paper-before.tex.txt';assert not backup.exists();backup.write_bytes(old)
s=old.decode('utf-8');before=s
def change(a,b):
 global s
 assert s.count(a)==1,(a[:90],s.count(a))
 s=s.replace(a,b)
change('Explicit odd-length snakes show that a uniform pair floor ten is false.',
 'Explicit odd-length snakes show that a uniform pair floor ten is false. A nine-transition exclusion removes one recorded competing cycle.')
change('Theorem~\\ref{thm:thirty-two-windows} limits the number of low-pair windows.\nThe following comparison',
 'Theorem~\\ref{thm:twenty-four-windows} limits the number of low-pair windows.\nThe following comparison')
change('Neither the proved allowance\n32 nor the proposed allowance 24 overcomes this obstruction. Further\nprogress must restrict the competing cycle, change the credit or improve\nthe global comparison.',
 'The proved allowance 24 does not overcome this obstruction in the original\ngraph. The exclusion below removes the recorded competing cycle. The\nproposition remains valid under its displayed hypotheses; its second cycle\nconstraint must be reassessed in the restricted graph.')
addition=r'''\subsection{Excluding the recorded seven-edge cycle}\label{sec:seven-cycle-exclusion}
\begin{theorem}\label{thm:nine-window-exclusion}
Let $x_r,\ldots,x_{r+9}$ be a fitting window of a snake in $\Q_9$ whose
transition word, after coordinate relabelling, is $012301430$.
The following conditions cannot hold simultaneously:
\[
\alpha_{r+3}\ge6,\qquad
(\alpha_{r+4},\alpha_{r+5},\alpha_{r+6},\alpha_{r+7},\alpha_{r+8})
=(3,3,3,5,2).
\]
There is no restriction on the parity of the path length or the window start.
\end{theorem}
\begin{proof}
Translate the first window vertex to zero and relabel the coordinates.
The window vertices become
\[
0,1,3,7,15,14,12,28,20,21.
\]
Every actual snake containing this window satisfies the necessary finite
local conditions: the prescribed vertices are selected, selected vertices
have degree one or two, at most two vertices are endpoints, and no selected
subset contains a cycle. The internal singleton counts are determined by
the twenty-one opposite corners from Lemma~\ref{lem:window-missing-corners}.
Impose the displayed counts and use the universal internal bound
twenty-one for the remaining counts.

The resulting Boolean system has a checked contradiction. Its retained
2353 clauses are justified by the local conditions, and all 1340 deductions
of the refutation have passed Lean. The interpretation of those clauses,
the coordinate normalization and the implication for arbitrary snakes have
also passed Lean. Hence an actual snake satisfying the displayed conditions
would give a satisfying assignment to a refuted system, a contradiction~\cite{sevencyclearchive}.
\end{proof}
The seven-edge cycle in Section~\ref{sec:odd-refined-model} contains the
word $012301430$ with stored counts $(6,3,3,3,5,2)$. Its first symbol
represents an actual count of at least six, so Theorem~\ref{thm:nine-window-exclusion}
excludes that row and prevents realization of this cycle by consecutive
windows of an actual snake. The four-edge cycle has no matching window.
Deleting the newly excluded rows therefore leaves the first profile's
minimum mean at 488: the old potential remains valid on the retained edges,
and that four-edge cycle still attains 488. The second profile requires a
new calculation; deleting its recorded attaining cycle alone gives no
strict improvement of its minimum mean.

A stronger candidate concerns the six-transition word $012301$ with its
five internal counts bounded above by $(3,3,3,5,2)$. Its finite contradiction
has passed an independent replay, but its complete Lean interpretation and
refutation remain pending. It is not used as a proved exclusion here.
Neither local result by itself establishes a smaller upper bound for $a(9)$.

'''
change('\\subsection{What an integer improvement requires}',addition+'\\subsection{What an integer improvement requires}')
change('checked for actual snakes. The $0123041$ six-count bound, necessary intervals',
 'checked for actual snakes. The nine-transition exclusion in\nTheorem~\\ref{thm:nine-window-exclusion} also applies to arbitrary snakes and\nremoves the recorded competing seven-edge cycle. The $0123041$ six-count bound, necessary intervals')
bib=r'''\bibitem{sevencyclearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{A checked nine-transition exclusion and the recorded seven-edge cycle}. Research record 138, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/138-seven-cycle-endpoints}.

'''
change('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==before.split('\\begin{document}',1)[0]
assert s.count('\\begin{definition}')==before.count('\\begin{definition}')
assert '.lean' not in s
new=s.encode('utf-8');editor.write_bytes(new);repo.write_bytes(new)
record=dict(status='SAVED_TARGETED_UPDATE',before_sha256=sha(old),after_sha256=sha(new),authors_and_preamble_unchanged=True,new_named_definitions=0,last_full_revision=136,targeted_revision=138,next_full_revision=146,actual_theorem_receipt_sha256=sha((H/'data/ActualBase138Minimal-audit.json').read_bytes()),pdf_rebuilt=False)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
