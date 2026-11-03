"""Add the range obstruction, preserving the open source and its preamble."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
q=json.loads((H/'data/Range143-audit.json').read_text());assert q['status']=='PASS' and len(q['axioms'])==7
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');repo=R/'paper/snake9_research.tex'
old=p.read_bytes();assert old==repo.read_bytes() and sha(p)=='a8052e82a7a46fb4b03dd510e34e269f81f3d4ae97488816562ec401d9bfa615'
backup=H/'audit/paper-before.tex.txt';assert not backup.exists();backup.write_bytes(old)
s=old.decode('utf-8')
addition=r"""\subsection{A necessary share floor after accounting for the range}\label{sec:share-floor-range}
The preceding cycle also limits the benefit of a weaker share theorem.
Six of its nine edges have canonical suffix $012034$, allowing reversal.
Increasing only the count-free share floor on that shape to $18$ raises
these six weights by $8,9,8,9,18,14$. The other additional share floors do
not change this cycle. A floor of $13$ would raise its total weight from
$4406$ to $4442$, which removes its zero-cost, zero-range obstruction.
A valid potential, however, must also satisfy the inequalities along each
subwalk~\cite{range143archive}.

\begin{proposition}\label{prop:share-fourteen-obstruction}
Keep the retained graph, its other weights, and its occurrence indicator
fixed. A count-free share floor of at most $14$ on $012034$, with any
nonnegative uniform occurrence credit, cannot reduce the existing comparison
below $235$, regardless of the choice of potential.
\end{proposition}
\begin{proof}
At floor $14$, the nine cycle weights are
\[
614,\ 494,\ 376,\ 734,\ 374,\ 492,\ 614,\ 374,\ 376.
\]
Their sum is $4448$. The last five edges form a walk of total weight $2230$.
No edge in the cycle carries an occurrence event. Hence every valid
mean and potential range satisfy
\[
\mu\le\frac{4448}{9},\qquad R\ge5\mu-2230.
\]
The first inequality follows by summing the nine potential inequalities
around the cycle. The second follows by summing along the five-edge walk
and bounding the difference between its endpoint potentials by $R$.
All weights on this cycle and walk can only decrease when the floor is
lowered, so both inequalities remain valid for every floor at most $14$.
For $\mu,C,B\ge0$, these two restrictions give
\[
\frac{1098960+8\mu+BC+R}{4200+\mu}
\ge\frac{1096730+13\mu}{4200+\mu}
\ge\frac{4964197}{21124}
=235+\frac{57}{21124}>235.
\]
The middle ratio decreases with $\mu$ on this domain. The graph uses
$B=24$. Lean checks the cycle summation, the walk summation, and the
comparison implications. The concrete saved graph rows and their weights
were checked separately.
\end{proof}

For the nine-cycle alone, floor $15$ gives mean $4454/9$ and minimum
range $2173/9$ at that mean. Their comparison is
$235-1245/42254$. Thus $15$ is the first integer floor not excluded by this
cycle and its subwalks. This is not a sufficiency result for the full graph.
Floor $18$ remains the existing requirement in the retained conditional
profile, and is the selected next local theorem target.

A separate contradiction query for the weaker floor $13$ used five broad
count intervals $[0,21]$, share cap $12$, and no added cycle exclusions.
Its dependency-trimmed Boolean certificate has 29165 deductions and
1699457 propagation hints; two direct replays end in the empty clause.
The Lean interpretation and replay had passed 23 of 231 planned modules
when the stronger range obstruction made the weaker target insufficient
for the comparison. The partial proof and all certificates are preserved.
No actual-snake share-$13$ theorem is claimed. This calculation establishes
a necessary threshold for the fixed graph argument, with no new global
upper bound and no claim of an optimal range on the full graph.

"""
marker='\\subsection{What an integer improvement requires}'
assert s.count(marker)==1;s=s.replace(marker,addition+marker)
bib=r"""\bibitem{range143archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{A cycle and subwalk obstruction to small empty-square share floors}. Research record 143, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/143-countfree-share13}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.decode().split('\\begin{document}',1)[0]
assert s.count('\\begin{definition}')==old.decode().count('\\begin{definition}')
p.write_bytes(s.encode('utf-8'));repo.write_bytes(p.read_bytes())
rec=dict(status='SAVED_TARGETED_UPDATE',before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),authors_and_preamble_unchanged=True,new_named_definitions=0,last_full_revision=136,targeted_revision=143,next_full_revision=146,pdf_rebuilt=False)
(H/'data/paper-revision.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8');print(json.dumps(rec))
