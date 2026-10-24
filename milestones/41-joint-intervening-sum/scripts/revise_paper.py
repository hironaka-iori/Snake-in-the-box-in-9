"""Promote the checked sum12 statement, retaining sum24 as a numerical question."""
from pathlib import Path
import json,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
v=json.loads((HERE/'data/verification.json').read_text());assert v['status']=='PASSED' and v['audited_theorems']==10
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip()
assert subprocess.check_output(['git','show',commit+':milestones/41-joint-intervening-sum/data/verification.json'],cwd=ROOT)
p=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert p.read_bytes()==editor.read_bytes();s=p.read_text(encoding='utf-8')
assert r'\label{prop:joint-intervening}' not in s
old=r'Further numerical tests suggest, under the same two hypotheses, that $\alpha_{r+3}+\alpha_{r+6}\ge12$ and $\sum_{j=2}^{6}\alpha_{r+j}\ge24$. Local forests attain the two proposed thresholds. These joint estimates require separate proof certificates and counter interpretations; they are not consequences of the two individual bounds of five and are not used in any theorem here.'
assert old in s
new=r'''The joint sum admits a stronger conclusion than adding the two individual lower bounds.

\begin{proposition}[Joint intervening-count bound]\label{prop:joint-intervening}
Under the hypotheses of Proposition~\ref{prop:intervening-counts},
\[
\alpha_{r+3}+\alpha_{r+6}\ge12.
\]
\end{proposition}
\begin{proof}[Computer-assisted proof]
Normalize the same eight-transition window. At the third and sixth internal centres, list the 21 eligible opposite corners. Concatenate the two lists, retaining the multiplicity of any repeated vertex. A corner contributes one precisely when it is absent from the selected set. Therefore the number of absent entries in this 42-entry list is exactly the sum of the two singleton counts. This identity follows by counting each list separately and adding; its general version for any finite list of centres has been checked in Lean.

Assume for contradiction that the joint sum is at most 11. Add the corresponding threshold counter to the ordinary local conditions, retaining only the two distant-count upper bounds of three. The counter clauses are justified by their actual input count, using the threshold-counter argument of Proposition~\ref{prop:window-counter}. The joint counter is interpreted separately from the endpoint and individual-count counters. This ensures that its assumed bound is exactly the hypothetical singleton sum.

Every induced path realizing the window would satisfy these clauses and the retained cycle exclusions. The extracted input has 4097 clauses and 1401 variables. A resolution refutation with 5222602 antecedent references was replayed in 174 segments, grouped into 29 kernel checks. The exact preservation of both singleton counts under translation and coordinate permutation transfers the contradiction to arbitrary coordinate labels. The counter interpretation, refutation, and arbitrary-snake deduction have all passed their recorded Lean checks~\cite{jointinterveningarchive}. Thus the assumed upper sum of 11 is impossible.
\end{proof}

A saved local forest with counts $(3,5,6,8,10,6,3)$ attains joint sum 12. Its induced degrees, endpoint conditions, acyclicity, and singleton counts have an independent check. Extension to a complete snake remains unresolved.

\begin{corollary}[Joint-count excess contribution]\label{cor:joint-intervening-excess}
Write $b_j=\min\{6,\alpha_j\}$ and $\delta_j=\alpha_j-b_j$. Let $J$ be a set of starting positions, in a fixed orientation of the path, satisfying the hypotheses of Proposition~\ref{prop:joint-intervening} and
\[
b_{r+3}+b_{r+6}\le11.
\]
Then
\[
|J|\le2\sum_{j=0}^{m}\delta_j,
\qquad
G_{12}\ge24\sum_{j=0}^{m}b_j+12|J|+\sum_{x\in S}\sigma_{12}(x).
\]
\end{corollary}
\begin{proof}
For each $r\in J$, subtract the upper bound on the two truncated counts from the lower bound of 12 on the actual counts. This gives $\delta_{r+3}+\delta_{r+6}\ge1$. Each fixed path position can appear at most once at offset three and at most once at offset six, since both maps $r\mapsto r+3$ and $r\mapsto r+6$ are injective. Summing over $J$ gives the first inequality. Substitute $T=\sum_j b_j+\sum_j\delta_j$ into $G_{12}=24T+\sum_x\sigma_{12}(x)$ and use $24\sum_j\delta_j\ge12|J|$. The excess implication, finite-set summation, and charge arithmetic have also been checked in Lean.
\end{proof}

The excess in this corollary is the same budget used by other count-excess estimates. Adding their bonuses requires a common multiplicity argument. No positive lower bound on $|J|$ has been established. An independent check of the 131 published bank paths finds 1442 oriented occurrences of the direction pattern, but none satisfies both distant-count caps. This observation supplies no frequency theorem.

The further estimate $\sum_{j=2}^{6}\alpha_{r+j}\ge24$ under the same two caps remains numerical. A local forest attains 24, but the exclusion below 24 still requires its own counter interpretation and proof replay. It is not used in the preceding propositions or the global upper bound.'''
s=s.replace(old,new,1)
anchor='The intervening-count restrictions have eight additional dependency audits,'
s=s.replace(anchor,'The joint intervening-count bound and its excess accounting have ten additional dependency audits, including the general concatenated-counter identity and exact count transport. '+anchor,1)
bib='\\bibitem{jointinterveningarchive}\nSnake-in-the-box project contributors, joint intervening-count proof and excess accounting, 24 October 2026.\n\\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/'+commit+'/milestones/41-joint-intervening-sum}.\n\n'
s=s.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
p.write_text(s,encoding='utf-8',newline='\n');editor.write_bytes(p.read_bytes())
print('Updated the paper and existing editor, citing',commit)
