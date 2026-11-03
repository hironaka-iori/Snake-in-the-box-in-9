"""Record the checked joint-floor restriction and the precise certificate status."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/JointFloors145-audit.json')['status']=='PASS'
assert read(H/'data/direct-replay.json')['status']=='PASS_COMPLETE_DIRECT_RUP_REPLAY'
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'); repo=R/'paper/snake9_research.tex'
old=p.read_bytes();assert old==repo.read_bytes()
assert sha(old)=='64120a8344a601d087b0ed8c642db901da02c124725c7f69da3d969825a7a6dd'
backup=H/'audit/paper-before.tex.txt';assert not backup.exists();backup.write_bytes(old)
s=old.decode('utf-8')
addition=r'''\subsection{A necessary relation between two share floors}\label{sec:joint-share-floors}
The same fourteen-cycle gives a more precise restriction on the next share
targets. Keep the graph and all other edge weights fixed. Let $F\ge11$ and
$G\ge4$ be the proposed count-free floors for $012301$ and $012340$,
respectively, in the existing resolution-twelve units. The cycle weights become
\[
256,\ 240+F,\ 736,\ 496,\ 360+F,\ 736,\ 360+G,\
496,\ 480+F,\ 376,\ 736,\ 360+F,\ 496,\ 720+G.
\]
The cycle has no occurrence events and no $012034$ suffix in either
orientation. Its weights are therefore independent of the uniform occurrence
credit and of any further change to the $012034$ floor.

\begin{proposition}\label{prop:joint-share-necessary}
Under these fixed-graph assumptions, a potential comparison strictly below
$235$ requires
\begin{equation}\label{eq:joint-share-necessary}
457F+225G>9848+7BC.
\end{equation}
Here $B\ge0$ is the occurrence allowance, $C\ge0$ its uniform credit,
$\mu\ge0$ the certified mean, and $R\ge0$ the potential range.
\end{proposition}
\begin{proof}
Summing around the cycle gives
\[
7\mu\le3424+2F+G.
\]
Its first two consecutive edges have total weight $496+F$.
Summing their potential inequalities and bounding the difference between
their endpoint potentials by $R$ gives
\[
2\mu\le496+F+R.
\]
A comparison below $235$ is equivalent to
$111960+BC+R<227\mu$. Substituting the range inequality yields
$111464-F+BC<225\mu$. Multiplication by seven followed by the cycle
mean bound gives~\eqref{eq:joint-share-necessary}. Lean checks these
implications. A separate saved-cycle calculation checks the edge weights
and their source identities~\cite{share145archive}.
\end{proof}

Three consequences guide the next computation. First, keeping the effective
$012340$ floor at $4$, even increasing $F$ to $19$ leaves the comparison at least
\[
\frac{7723775}{32866}=235+\frac{265}{32866}.
\]
The same lower bound holds for smaller $F$, since the cycle edge weights
are then no larger. Second, with $F=16$ and integer $G$, a successful
comparison requires $G\ge12$. Third, with $F=G=16$ and the existing
allowance $B=24$, it requires $C<19/3$. These are necessary conditions.
They do not show that the remaining floors or credits suffice for the
full graph, nor do they establish an improved bound for arbitrary snakes.

The saved Boolean certificate for $012301$ at cap $15$ has now been
converted and independently replayed in full: $285541$ deductions and
$31017505$ propagation references yield a contradiction from $12977$
original core clauses. The original input has $11378$ variables and
$92656$ clauses, including sixteen exclusions of induced eight-cycles;
six of these exclusions occur in the retained core. The count intervals
are all $[0,21]$. Interpreting this contradiction as a share-$16$ theorem
still requires the complete Lean replay and the actual-snake interpretation,
including the cycle exclusions.

For the earlier share-$18$ proof, all $104$ smaller database parts now
have checked truth-transfer arguments from the original clause chunks.
The complete assembly reached its time limit without a checked theorem.
The initial-database connection and the complete local proofs therefore
remain pending. The successful component checks and the complete Boolean
replay are recorded separately from those unresolved obligations.

'''
marker='\\subsection{What an integer improvement requires}'
assert s.count(marker)==1;s=s.replace(marker,addition+marker)
bib=r'''\bibitem{share145archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Joint share restrictions and a complete replay of the count-free certificate for 012301}. Research record 145, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/145-countfree-012301}.

'''
assert s.count('\\end{thebibliography}')==1;s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
new=s.encode('utf-8');assert old.split(b'\\begin{document}',1)[0]==new.split(b'\\begin{document}',1)[0]
p.write_bytes(new);repo.write_bytes(new)
record=dict(status='TARGETED_PAPER_UPDATE_145',before_sha256=sha(old),after_sha256=sha(new),
    new_named_definitions=0,preamble_and_hypersetup_unchanged=True,
    authors=['Iori Hironaka','Tommy Ma','Steven Zhan'],last_full_revision=136,next_full_revision=146,
    scope='Necessary fixed-graph tradeoff, complete native certificate, and unresolved Lean assembly stated separately.')
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
