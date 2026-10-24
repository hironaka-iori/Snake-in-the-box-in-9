"""Add the checked local theorem only after the milestone's completion gate passes."""
from pathlib import Path
import json,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
receipt=json.loads((HERE/'data/verification.json').read_text());assert receipt['status']=='PASSED' and receipt['audited_theorems']==8
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip()
assert subprocess.check_output(['git','show',commit+':milestones/40-intervening-counts/data/verification.json'],cwd=ROOT)
p=ROOT/'paper/snake9_research.tex';s=p.read_text(encoding='utf-8')
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert p.read_bytes()==editor.read_bytes()
assert r'\label{prop:intervening-counts}' not in s
insert=r'''
\subsection{Restrictions on the intervening counts}\label{sec:intervening-counts}
The two distant counts do not determine whether the intervening counts can occur together. The next restriction uses three specified positions at a time and the absence of selected cycles.

\begin{proposition}[Intervening-count lower bounds]\label{prop:intervening-counts}
Suppose an induced path has the eight transitions $(a,b,c,d,e,c,a,d)$ starting at $x_r$, where $a,b,c,d,e$ are distinct coordinates. If
\[
\alpha_{r+1}\le3,\qquad \alpha_{r+7}\le3,
\]
then
\[
\alpha_{r+3}\ge5,\qquad \alpha_{r+6}\ge5.
\]
\end{proposition}
\begin{proof}[Computer-assisted proof]
Translate $x_r$ to zero and map the five named directions, in order, to $0,1,2,3,4$. Extend this map to a permutation of the nine coordinates. The normalized window has vertex sequence
\[
(0,1,3,7,15,31,27,26,18).
\]
Use the radius-four local model from Section~\ref{sec:radius-four-236}. For the first assertion, impose upper bounds $(3,21,4,21,21,21,3)$ on its seven internal singleton counts. For the second, impose $(3,21,21,21,21,4,3)$. The value 21 places no additional restriction on an internal count. Thus the first model represents a hypothetical violation of the first conclusion under the two stated hypotheses, and the second represents a violation of the second conclusion.

The ordinary encoding excludes coordinate squares and induced six-cycles in three-dimensional faces. Add further finite cycle exclusions, all justified by Lemma~\ref{lem:subset-low-degree}. The first input includes 44 additional cycle exclusions. The second includes four additional translates of one induced ten-cycle, in the four unused coordinate directions. Every retained cycle clause and every degree, endpoint, and count clause follows from the induced-path conditions. The two extracted inputs have 2708 and 1419 clauses, respectively. Their resolution refutations, containing 1141561 and 86400 antecedent references, have been replayed by the sound proof checker. The geometric interpretations and coordinate normalization have also passed Lean checks~\cite{interveningarchive}. Hence both inputs are inconsistent, proving the two implications.
\end{proof}

Acyclicity is essential to this particular local argument. The degree-and-endpoint model for the first input admits a selected set of 142 vertices with counts $(3,5,4,7,12,10,3)$ and three selected cycles. Its saved vertex set has an independent count and degree check. It violates the proposed third-count conclusion, while satisfying the two distant-count caps; its cycles prevent it from being an induced path. Thus degree and endpoint conditions alone cannot establish this local implication.

Separate local forests have counts $(3,6,5,5,10,11,3)$ and $(3,6,10,9,6,5,3)$. They attain the individual lower thresholds of five. Extension of these forests to complete snakes is unresolved. Proposition~\ref{prop:intervening-counts} excludes the saved periodic diagnostic occurrence $(3,4,4,5,5,3,3)$, which the two-count inequalities admitted. Excluding this occurrence alone supplies no new uniform bound or certified minimum cycle mean.

Further numerical tests suggest, under the same two hypotheses, that $\alpha_{r+3}+\alpha_{r+6}\ge12$ and $\sum_{j=2}^{6}\alpha_{r+j}\ge24$. Local forests attain the two proposed thresholds. These joint estimates require separate proof certificates and counter interpretations; they are not consequences of the two individual bounds of five and are not used in any theorem here.

'''
anchor=r'\section{What a stronger upper bound still requires}'
assert anchor in s;s=s.replace(anchor,insert+anchor,1)
anchor='The asymmetric distance-four restrictions and their excess accounting have 17 further dependency audits;'
s=s.replace(anchor,'The intervening-count restrictions have eight additional dependency audits, covering both refutations, their geometric interpretations, and arbitrary coordinate normalization. '+anchor,1)
bib='\\bibitem{interveningarchive}\nSnake-in-the-box project contributors, intervening-count certificates and local configurations, 24 October 2026.\n\\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/'+commit+'/milestones/40-intervening-counts}.\n\n'
s=s.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
p.write_text(s,encoding='utf-8',newline='\n');editor.write_bytes(p.read_bytes())
print('Updated paper and existing editor; cited proof checkpoint',commit)
