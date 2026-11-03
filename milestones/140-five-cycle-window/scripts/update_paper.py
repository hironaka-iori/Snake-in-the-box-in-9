"""Update the open paper only after complete actual-snake proof verification."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
proof=json.loads((H/'data/proof-completion.json').read_text())
assert proof['status']=='PASS_ACTUAL_012032_WEAK_EXCLUSION'
q=json.loads((H/'data/Weak140Actual-audit.json').read_text());assert q['status']=='PASS' and q['exit_code']==0
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');repo=R/'paper/snake9_research.tex'
old=p.read_bytes();assert old==repo.read_bytes() and sha(p)=='493eaba63207b30e93814cc03ae5720f09d0c5521c5b16860faf2dba7c6006d9'
backup=H/'audit/paper-before.tex.txt';assert not backup.exists();backup.write_bytes(old)
s=old.decode('utf-8')
start=s.index('The five-cycle contains the canonical suffix $012032$ with internal counts')
end=s.index('\\subsection{What an integer improvement requires}',start)
addition=r"""The five-cycle contains a canonical $012032$ window with internal counts
$(3,5,4,5,3)$. The following exclusion removes this cycle and the earlier
four-cycle from the strengthened model.

\subsection{A further restriction on the five internal counts}\label{sec:five-count-exclusion}
\begin{theorem}\label{thm:alternate-three-four-three}
Let $x_r,\ldots,x_{r+6}$ be a fitting canonical $012032$ window in a snake
in $\Q_9$. If
\[
\alpha_{r+1}=3,\qquad \alpha_{r+3}=4,\qquad \alpha_{r+5}=3,
\]
then
\[
\alpha_{r+2}\ge6\quad\text{or}\quad\alpha_{r+4}\ge6.
\]
There is no restriction on the parity of the path or the positions of its endpoints.
\end{theorem}
\begin{proof}
Translate and permute coordinates so that the window vertices are
$0,1,3,7,6,14,10$. Each internal vertex has seven unused directions and
therefore twenty-one opposite corners. Its singleton-square count equals
the number of these corners absent from the path, by
Lemma~\ref{lem:window-missing-corners}.

Suppose both intervening counts are at most five. The five count intervals
are then $[3,3],[0,5],[4,4],[0,5],[3,3]$. The necessary conditions for the
selected vertices include degree at most two, positive degree, at most two
endpoints, these corner-count intervals, and exclusion of selected cycles.
A retained set of 4163 clauses from these conditions admits a contradiction
certificate of 18606 deductions. Its clauses and every deduction, followed
by their interpretation for an arbitrary snake, have been checked in Lean.
The checked interpretation uses the stated upper bounds of five; equality
at these two positions is unnecessary. The contradiction excludes the
assumed intervals and proves the disjunction~\cite{fivecount140archive}.
\end{proof}

The count vectors $(3,5,4,5,3)$ and $(3,5,4,4,3)$ are both excluded.
They occur in the saved five-cycle and the earlier four-cycle, respectively.
Recognition at the two available six-transition positions removes both
cycles. Reversal preserves the statement. The additional-share six-cycle
has no matching window and remains an obstruction for that profile.
These statements identify deleted cycles; the new graph minimum has not
yet been computed.

Removing the earlier four-cycle permits a new test with zero occurrence
credit. If the revised comparison has mean $496$ and potential range
$R<632$, then
\[
\frac{1098960+8\cdot496+R}{4200+496}<235.
\]
Cross-multiplication gives exactly the condition $R<632$; this arithmetic
has also passed Lean. The previous range $602$ was established for credit
$83/3$, so it supplies no zero-credit potential without a new edge check.
All inherited count and share hypotheses and the separate graph-to-snake
obligations remain. No smaller global upper bound follows yet.

"""
s=s[:start]+addition+s[end:]
a='A nine-transition exclusion removes one recorded competing cycle.'
b=a+' A further local theorem shows that alternate internal counts $3,4,3$ in a $012032$ window force one intervening count to be at least six.'
assert s.count(a)==1;s=s.replace(a,b)
bib=r"""\bibitem{fivecount140archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{A five-count exclusion and a revised zero-credit test}. Research record 140, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/140-five-cycle-window}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.decode('utf-8').split('\\begin{document}',1)[0]
assert s.count('\\begin{definition}')==old.decode('utf-8').count('\\begin{definition}')
p.write_bytes(s.encode('utf-8'));repo.write_bytes(p.read_bytes())
rec=dict(status='SAVED_TARGETED_UPDATE',before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),authors_and_preamble_unchanged=True,new_named_definitions=0,last_full_revision=136,targeted_revision=140,next_full_revision=146,pdf_rebuilt=False)
(H/'data/paper-revision.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8')
print(json.dumps(rec))
