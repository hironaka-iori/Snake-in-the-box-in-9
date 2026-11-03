"""Record the failed credit hypothesis and the checked fixed-model obstruction."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
q=json.loads((H/'data/Obstruction142-audit.json').read_text())
assert q['status']=='PASS' and len(q['axioms'])==8
assert json.loads((H/'data/result-review.json').read_text())['status']=='PASS_BOUNDED_SAVED_RESULT_REVIEW'
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');repo=R/'paper/snake9_research.tex'
old=p.read_bytes();assert old==repo.read_bytes() and sha(p)=='86ee96b764b28e65d557d70a91e008f5d7823ebb0ea9c2d4d4aba987d5c8b83f'
backup=H/'audit/paper-before.tex.txt';assert not backup.exists();backup.write_bytes(old)
s=old.decode('utf-8')
start=s.index('The next completed-share test is therefore $C=533/12$.')
end=s.index('\\subsection{What an integer improvement requires}',start)
addition=r"""The completed-share test at $C=533/12$ has now been evaluated on all
4661572 retained edges. Its minimum mean is $4406/9$, with a potential
range $5377/9$, giving the comparison
\[
\frac{1098960+8(4406/9)+24(533/12)+5377/9}{4200+4406/9}
=\frac{9940859}{42206}>235.
\]
Thus the proposed mean $3011/6$ is not attained. The zero-credit
additional-share comparison remains $551765/2348<235$; the positive-credit
test changes no premise of that separate calculation.

\begin{proposition}\label{prop:zero-event-nine-cycle}
For the retained completed-share graph, adding any nonnegative uniform
credit to the same low-pair occurrence indicator cannot reduce the existing
upper comparison below $235$.
\end{proposition}
\begin{proof}
An attaining nine-edge cycle has original weights
\[
610,\ 489,\ 376,\ 730,\ 369,\ 492,\ 600,\ 364,\ 376.
\]
Their sum is $4406$, and none of its edges carries the occurrence indicator.
The cycle survives for every choice of the uniform credit, so the minimum
mean always satisfies $\mu\le4406/9$. For $\mu,C,B,R\ge0$ and this mean cap,
\[
\frac{1098960+8\mu+BC+R}{4200+\mu}
\ge\frac{4962944}{21103}
=235+\frac{3739}{21103}>235.
\]
Indeed, the denominator is positive, the term $BC+R$ is nonnegative,
and $(1098960+8\mu)/(4200+\mu)$ decreases with $\mu$.
The graph uses $B=24$, although the inequality holds for every $B\ge0$.
The exact saved cycle, its nine zero slacks, and its zero indicators were
independently checked against original graph rows. Lean checks the rational
inequality under the stated mean cap~\cite{credit142archive}.
\end{proof}

This proposition concerns the fixed graph and its specified credit indicator.
The cycle is a finite-graph obstruction; it is not asserted to describe a
realizable periodic snake. A new local exclusion or a larger justified
empty-square share on these windows could change its mean. Even before
accounting for credit cost or potential range, increasing its total weight
by $\Delta\ge0$ must satisfy
\[
\Delta>\frac{7478}{227}
\]
to remove this cycle's obstruction to a comparison below $235$. Thus an
integer increase must be at least $33$. This is only a necessary condition;
other cycles and the potential range can require more. Lean checks this
arithmetic implication as well. The next investigation therefore concerns
empty-square shares on the nine-cycle's windows. Further uniform-credit
tuning on this unchanged graph has been ruled out.

The evaluator checks every edge inequality and an attaining cycle. The
independent review reconstructs 40 selected original rows and checks the
saved cycle and comparison; it does not repeat the complete edge scan.
Potential-range optimality, a full Lean graph certificate, and the complete
comparison for arbitrary snakes remain unresolved. No new unconditional
upper bound is obtained in this test.

"""
s=s[:start]+addition+s[end:]
bib=r"""\bibitem{credit142archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{A zero-event nine-cycle obstructing uniform occurrence credit}. Research record 142, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/142-retuned-occurrence-credit}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.decode('utf-8').split('\\begin{document}',1)[0]
assert s.count('\\begin{definition}')==old.decode('utf-8').count('\\begin{definition}')
p.write_bytes(s.encode('utf-8'));repo.write_bytes(p.read_bytes())
rec=dict(status='SAVED_TARGETED_UPDATE',before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),authors_and_preamble_unchanged=True,new_named_definitions=0,last_full_revision=136,targeted_revision=142,next_full_revision=146,pdf_rebuilt=False)
(H/'data/paper-revision.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8');print(json.dumps(rec))
