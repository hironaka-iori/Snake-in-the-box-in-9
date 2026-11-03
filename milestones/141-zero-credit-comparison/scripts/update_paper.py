"""Record the completed zero-credit calculation without changing mathematical definitions."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result=json.loads((H/'data/five-cycle-zero/results.json').read_text());assert result['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
review=json.loads((H/'data/result-review.json').read_text());assert review['status'].startswith('PASS')
q=json.loads((H/'data/Comparison141-audit.json').read_text());assert q['status']=='PASS' and len(q['axioms'])==8
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');repo=R/'paper/snake9_research.tex'
old=p.read_bytes();assert old==repo.read_bytes() and sha(p)=='b47755a40dde4b639585b9420c06cc79d5bd9836f9748e71c8c0332359b24a28'
backup=H/'audit/paper-before.tex.txt';assert not backup.exists();backup.write_bytes(old)
s=old.decode('utf-8')
start=s.index('Removing the earlier four-cycle permits a new test with zero occurrence')
end=s.index('\\subsection{What an integer improvement requires}',start)
addition=r"""\subsection{Zero occurrence credit after the five-count exclusion}\label{sec:zero-credit-exclusion}
Apply Theorem~\ref{thm:alternate-three-four-three} at both available
six-transition positions and in both orientations. This deletes 200 further
edges, leaving 4661572. Every rejected count symbol is below six, so the
stored symbols specify the required actual counts. Set the occurrence
credit to zero and retain the previous local hypotheses and share weights.
The exact finite-graph calculation gives~\cite{zerocredit141archive}:
\begin{center}
\begin{tabular}{lccc}
\toprule
Profile & Minimum mean & Potential range & Comparison\\
\midrule
Completed shares & $3424/7$ & $4159/7$ & $7724271/32824$\\
Additional shares & $496$ & $602$ & $551765/2348$\\
\bottomrule
\end{tabular}
\end{center}
The evaluator checks every edge inequality and an attaining cycle for each
mean. An independent review checks every new deletion, selected original
rows, cycle weights and adjacency, potential hashes and ranges, and the
comparison arithmetic. It does not repeat the full edge scan. The old
additional-share six-cycle survives; the reported attaining six-cycle is
a different cycle with the same mean.

For zero occurrence credit, the comparison is
$(1098960+8\mu+R)/(4200+\mu)$. The second fraction satisfies
\[
\frac{551765}{2348}=235-\frac{15}{2348}<235,
\]
whereas the first lies strictly between 235 and 236. Lean checks these
arithmetic statements and the resulting integer bounds, assuming the
corresponding comparison for the path length. This recovers a conditional
comparison with integer part 234. Both profiles still use the inherited
count-sum hypotheses, the proposed six-count floor, and the odd-length
pair restriction; the second also uses its additional share floors.
The complete graph-to-snake comparison and a full Lean potential certificate
remain separate obligations. No smaller unconditional bound follows here.

The completed-share profile now has a seven-edge cycle with total weight
3424 and two low-pair events. A surviving eighteen-edge cycle has mean
$3011/6$ and no such event. Thus a nonnegative uniform occurrence credit
$C$ leaves the restrictions
\[
\mu\le\frac{3424+2C}{7},\qquad \mu\le\frac{3011}{6}.
\]
For nonnegative $C,\mu,R$, these two restrictions imply
\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge\frac{6624244}{28211}.
\]
Indeed, substituting $24C\ge84\mu-41088$ bounds the ratio below by
$(1057872+92\mu)/(4200+\mu)$, which decreases with $\mu$ on this domain.
The bound is attained in this arithmetic relaxation at
$C=533/12$, $\mu=3011/6$, and $R=0$. These implications have passed Lean;
attainment by the actual graph is not asserted.

The next completed-share test is therefore $C=533/12$. At the target mean
$3011/6$, the comparison is below 235 exactly when $R<5341/6$. Other cycles
may force a smaller mean, and a potential at this credit has not yet been
calculated. The zero-credit additional-share result remains available while
this separate parameter choice is tested on the completed-share profile.

"""
s=s[:start]+addition+s[end:]
bib=r"""\bibitem{zerocredit141archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Zero occurrence credit after the five-count exclusion}. Research record 141, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/141-zero-credit-comparison}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.decode('utf-8').split('\\begin{document}',1)[0]
assert s.count('\\begin{definition}')==old.decode('utf-8').count('\\begin{definition}')
p.write_bytes(s.encode('utf-8'));repo.write_bytes(p.read_bytes())
rec=dict(status='SAVED_TARGETED_UPDATE',before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),authors_and_preamble_unchanged=True,new_named_definitions=0,last_full_revision=136,targeted_revision=141,next_full_revision=146,pdf_rebuilt=False)
(H/'data/paper-revision.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8');print(json.dumps(rec))
