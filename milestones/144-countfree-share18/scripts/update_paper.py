"""Add the audited share18 experiment and its stronger cycle obstruction."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
assert read(H/'experiments/data/RetunedObstruction144-audit.json')['status']=='PASS'
assert read(H/'data/retuned-review.json')['status']=='PASS_BOUNDED_RETUNED_CYCLE_REVIEW'
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');repo=R/'paper/snake9_research.tex'
old=p.read_bytes();assert old==repo.read_bytes() and sha(p)=='3c28f1f645cab1969107557429eabe36d7a36f471a3a2f9fe6d3567bd4cc4d92'
backup=H/'audit/paper-before.tex.txt';assert not backup.exists();backup.write_bytes(old)
s=old.decode('utf-8')
addition=r"""\subsection{A cycle unaffected by the selected share and occurrence credits}\label{sec:share18-unaffected-cycle}
The next experiment isolates the effect of the proposed count-free share
floor $18$ for $012034$. It retains the graph and every other weight from
the completed-share profile. At zero occurrence credit, the exact finite-graph
calculation gives mean $5399/11$ and potential range $593$, hence comparison
\[
\frac{12138275}{51599}=235+\frac{12510}{51599}.
\]
Its attaining eleven-cycle contains four occurrence events and no $012034$
suffix. Combining that cycle with the preceding nine-cycle suggests testing
the occurrence credit $C=601/36$. The two cycles alone admit mean $4472/9$
and range $4391/18$, with comparison $235-3405/84544$. These parameters
were therefore a candidate for the full graph, with no sufficiency claim.

The full-graph test instead returns mean $3445/7$ and range $608$, giving
\[
\frac{23182022}{98535}=235+\frac{26297}{98535}.
\]
Its attaining fourteen-cycle has no occurrence events and no $012034$
suffix in either orientation. This produces a stronger obstruction than
the numerical failure of that particular credit~\cite{share144archive}.

\begin{proposition}\label{prop:share18-independent-obstruction}
Keep this retained graph, its other completed-share weights, and its
occurrence indicator fixed. Changing only the count-free share floor for
$012034$ and the nonnegative uniform occurrence credit cannot reduce the
existing comparison below $235$.
\end{proposition}
\begin{proof}
The fourteen-cycle has the unscaled weights
\[
256,\ 246,\ 736,\ 496,\ 371,\ 736,\ 364,\
496,\ 486,\ 376,\ 736,\ 371,\ 496,\ 724.
\]
Their sum is $6890$. Its six-transition suffixes consist of eight copies
of $012304$, four of $012301$, and two of $012340$, where shapes are
identified up to coordinate relabelling and reversal. Thus neither of the
two permitted changes alters any of its weights. Summing the potential
inequalities around the cycle gives $14\mu\le6890$, or $\mu\le3445/7$.
For $\mu,C,B,R\ge0$, the comparison consequently satisfies
\[
\frac{1098960+8\mu+BC+R}{4200+\mu}
\ge\frac{1098960+8\mu}{4200+\mu}
\ge\frac{1544056}{6569}
=235+\frac{341}{6569}>235.
\]
The second ratio decreases with $\mu$ on this domain. The existing
occurrence allowance is $B=24$. Lean checks the cycle summation and the
comparison implications. A separate audit reconstructs the fourteen saved
rows from the source graph and checks closure, shapes, weights and absence
of occurrence events. The computation checks the potential inequalities
on all $4661572$ retained edges; the independent audit checks the saved
cycle and potential range, without claiming a second full-graph verification.
\end{proof}

This proposition restricts the chosen comparison method. It gives no
improved upper bound for arbitrary snakes. Progress within this graph
requires another share contribution or an exclusion affecting the surviving
cycle. The conditional profile using all additional share floors remains
separate and is not contradicted by this obstruction.

The selected share-$18$ claim also has a preserved Boolean contradiction
certificate. Its input uses $11924$ variables and $96091$ clauses, five
broad count intervals $[0,21]$, radius four, resolution twelve, and share
cap $17$. The independently checked certificate contains $145215$
deductions, $14710881$ propagation references and $13224$ original core
clauses. Its complete Lean interpretation remains pending. The first
export passed six modules before memory pressure stopped the replay.
A direct initial-database construction has a checked general soundness
argument; a separately materialized database passes a $6006$-reference
prefix check. The link from the latter representation to truth of the
original clauses, the remaining replay, and the actual-snake interpretation
are still required. No completed local share-$18$ theorem is claimed.

"""
marker='\\subsection{What an integer improvement requires}'
assert s.count(marker)==1;s=s.replace(marker,addition+marker)
bib=r"""\bibitem{share144archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{A count-free share certificate and a cycle unaffected by the selected credits}. Research record 144, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/144-countfree-share18}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.decode().split('\\begin{document}',1)[0]
assert s.count('\\begin{definition}')==old.decode().count('\\begin{definition}')
p.write_bytes(s.encode());repo.write_bytes(p.read_bytes())
record=dict(status='SAVED_TARGETED_UPDATE',before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),authors_and_preamble_unchanged=True,new_named_definitions=0,last_full_revision=136,targeted_revision=144,next_full_revision=146,pdf_rebuilt=False)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
