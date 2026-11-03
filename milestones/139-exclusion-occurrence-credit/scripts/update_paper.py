from pathlib import Path
import hashlib,json
H=Path('milestones/139-exclusion-occurrence-credit');R=H.resolve().parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ['Credit139','Obstruction139','OptimalCredit139']:
 q=json.loads((H/'data'/(name+'-audit.json')).read_text())
 assert q['status']=='PASS' and q['exit_code']==0
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');repo=R/'paper/snake9_research.tex'
old=p.read_bytes();assert old==repo.read_bytes()
assert sha(p)=='69d6ee520bfe8c1a1920d45f3ae9c7c2b5b5654232ac9982fabd56c12982bec6'
(H/'audit/paper-before.tex.txt').write_bytes(old)
s=old.decode('utf-8')
addition=r'''\subsection{Uniform credit after the new exclusion}\label{sec:credit-after-exclusion}
Delete the row excluded by Theorem~\ref{thm:nine-window-exclusion} and add
credit $83/3$ for each suffix $012032$ window whose two relevant count
symbols are both below six and have sum at most nine. These exact symbols
certify actual low-pair windows. Distinct suffix starts are distinct path
starts, so Theorem~\ref{thm:twenty-four-windows} bounds their number by 24.
The truncation implication and this transfer of the occurrence bound have
passed Lean.

Exact integer calculations on the remaining 4661772 edges give the
following results. The old local hypotheses, including the odd-length
pair floor and the proposed six-count floor, remain in force.
\begin{center}
\begin{tabular}{lccc}
\toprule
Profile & Minimum mean & Potential range & Comparison\\
\midrule
Completed shares & $2446/5$ & $2973/5$ & $5520661/23446$\\
Additional shares & $496$ & $602$ & $552097/2348$\\
\bottomrule
\end{tabular}
\end{center}
The computation checks every potential inequality and an attaining cycle
for each mean. An independent review reconstructs the saved cycles and
checks their weights, adjacency, potential values and arithmetic; it does
not repeat the full edge scan. The two attaining cycles have five and six
edges respectively, and neither receives occurrence credit. Both displayed
comparisons exceed 235. These remain finite-model calculations~\cite{credit139archive}.

The five-cycle's unchanged mean bounds the completed profile by
$\mu\le2446/5$ for every nonnegative uniform credit $C$. The surviving
four-cycle also gives $\mu\le488+C/2$. Consequently, for $\mu,R\ge0$,
\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge \frac{2757328}{11723}>235.
\]
Indeed, $C\ge2\mu-976$ bounds the first ratio below by
$(1075536+56\mu)/(4200+\mu)$. Cross-multiplication shows that this expression
decreases with $\mu$, so substitution of $\mu=2446/5$ proves the displayed
bound. Equality in this arithmetic relaxation occurs at
$C=12/5$, $\mu=2446/5$ and $R=0$. No graph potential attaining these
parameters is asserted.

More generally, the five-cycle prevents this comparison from reaching 235
even with any nonnegative occurrence allowance. For the additional-share
profile, its unchanged six-cycle gives $\mu\le496$ and prevents the analogous
comparison from reaching 234. These arithmetic implications have passed
Lean. They limit uniform credit on the specified graph and weight profiles;
new exclusions, different credits and different charge comparisons remain
outside their scope.

The five-cycle contains the canonical suffix $012032$ with internal counts
$(3,5,4,5,3)$. Its relevant pair sums to ten, so the present low-pair endpoint
theorem supplies no consequence for this window. A scan of 135 saved snakes
found no exact match. This finite observation leaves its feasibility open
and identifies the next local test; it supplies no exclusion theorem.

'''
anchor='\\subsection{What an integer improvement requires}'
assert s.count(anchor)==1;s=s.replace(anchor,addition+anchor)
bib=r'''\bibitem{credit139archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Uniform occurrence credit after the nine-transition exclusion}. Research record 139, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/139-exclusion-occurrence-credit}.

'''
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.decode('utf-8').split('\\begin{document}',1)[0]
assert s.count('\\begin{definition}')==old.decode('utf-8').count('\\begin{definition}')
p.write_bytes(s.encode('utf-8'));repo.write_bytes(p.read_bytes())
rec=dict(status='SAVED_TARGETED_UPDATE',before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),authors_and_preamble_unchanged=True,new_named_definitions=0,last_full_revision=136,targeted_revision=139,next_full_revision=146,pdf_rebuilt=False)
(H/'data/paper-revision.json').write_text(json.dumps(rec,indent=2)+'\n')
src=Path('milestones/138-seven-cycle-endpoints/scripts/check_paper_source.py').read_text().replace('milestones/137-actual-block-assembly/data/paper-source-review.json','milestones/138-seven-cycle-endpoints/data/paper-source-review.json')
(H/'scripts/check_paper_source.py').write_text(src,encoding='utf-8')
print(json.dumps(rec))
