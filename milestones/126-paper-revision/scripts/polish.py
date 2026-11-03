"""Small clarity changes after the bounded mathematical reviews."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'paper/snake9_research.tex'; E=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
t=P.read_text(encoding='utf-8');assert P.read_bytes()==E.read_bytes()
def repl(a,b):
 global t
 assert t.count(a)==1,(t.count(a),a[:100]);t=t.replace(a,b)
repl('The deductions and their application to actual snakes have passed\nLean~\\cite{uniformsixarchive,criticalsixarchive}.','The corresponding actual-snake count and incidence deductions have passed\nLean; the checked incidence convention counts four anchored occurrences\nper empty square~\\cite{uniformsixarchive,criticalsixarchive}.')
repl('Both statements for arbitrary snakes have passed Lean~\\cite{criticalsixarchive}.','The corresponding actual-snake count and incidence deductions have passed\nLean, with four anchored occurrences per empty square~\\cite{criticalsixarchive}.')
repl(r'''Suppose the six transitions use distinct directions and the five internal singleton counts satisfy
\[
(\alpha_1,\alpha_2,\alpha_3,\alpha_4)=(4,5,4,2),
\qquad 6\le\alpha_5\le21.
\]
Then $H\ge120$.''',r'''Suppose $r+6\le m$ and the six transitions beginning at $x_r$ use distinct
directions. If
\[
(\alpha_{r+1},\alpha_{r+2},\alpha_{r+3},\alpha_{r+4})=(4,5,4,2),
\qquad 6\le\alpha_{r+5}\le21,
\]
then $\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge120$.''')
repl(r'''Let $B=\sum_jb_j$, $D=\sum_j\delta_j$, and $G=24(B+D)+\Sigma$. Suppose nonnegative demands $Q,C,R$ satisfy
\[
Q\le7D,\qquad6C\le\Sigma,\qquad R\le7(24D+\Sigma).
\]
Then
\[
168B+R\le7G,\qquad
336B+24Q+42C+R\le14G.
\]''',r'''Put $B=\sum_jb_j$ and $\Sigma=\sum_j\sigma_{12}(x_j)$. Suppose nonnegative
demands $Q,C,R$ satisfy
\[
Q\le7\sum_j\delta_j,\qquad6C\le\Sigma,\qquad
R\le7\left(24\sum_j\delta_j+\Sigma\right).
\]
Then
\[
168B+R\le7G_{12},\qquad
336B+24Q+42C+R\le14G_{12}.
\]''')
repl(r'The first bound follows by substitution. For the second, use $24Q\le168D$, $42C\le7\Sigma$, and the assumed bound on $R$. The right side becomes $336B+336D+14\Sigma=14G$.',r'The first bound follows by substitution into $G_{12}=24(B+\sum_j\delta_j)+\Sigma$. For the second, use $24Q\le168\sum_j\delta_j$, $42C\le7\Sigma$, and the assumed bound on $R$. The right side becomes $336B+336\sum_j\delta_j+14\Sigma=14G_{12}$.')
repl('Two more specific five-count restrictions on $012304$ have independently\nreplayed negative certificates, with their complete Lean deductions still\npending~\\cite{latersumarchive}.',r'''Two narrower $012304$ hypotheses require total at least 23 when
$(\alpha_{r+1},\alpha_{r+3},\alpha_{r+4})=(2,2,3)$ or $(2,4,2)$,
respectively, with $\alpha_{r+2},\alpha_{r+5}\ge6$ in both cases.
Their negative certificates have independent native replays, while their
complete Lean deductions remain pending. These are the twelfth and
thirteenth sum rules~\cite{latersumarchive}.''')
repl('The final attaining cycles have 26 and six edges.','The attaining cycles for this ten-rule stage have 26 and six edges.')
repl('The conditional-share mean is below the second, since',r'The later completed-share mean is also below the first threshold, since $111960\cdot6-227\cdot2915=10055>0$. The conditional-share mean is below the second, since')
b=t.encode('utf-8');P.write_bytes(b);E.write_bytes(b)
j=json.loads((H/'data/revision.json').read_text());j.update(paper_sha256=hashlib.sha256(b).hexdigest(),polish='Clarified anchored-square verification scope, explicit share indices, removed temporary z/G/D aliases, distinguished graph stages.')
(H/'data/revision.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print(j['paper_sha256'])
