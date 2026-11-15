from pathlib import Path
import re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
main=r'''
\subsection{Exact limits of degree and cycle inequalities}
\label{sec:linear219}
The next calculation concerns the same fixed parent and the same two
joining endpoints. Its purpose is to determine whether linear degree
and cycle inequalities can exclude the 94-vertex partner target.
For each allowed vertex $u$, let $x_u$ indicate selection and let $e_u$
indicate the free endpoint; $e_u=0$ at even vertices other than the root.
The root is selected with degree one, and the odd endpoint indicators
sum to one. Selection has equal totals in the two parity classes.
All variables are subsequently allowed to range over $[0,1]$.

At a nonroot vertex of available degree $d_u$, put
$s_u=\sum_{v\sim u}x_v$. Conditional selected degree has the exact
Boolean encoding
\[
2x_u-e_u\le s_u\le d_u-(d_u-2)x_u-e_u,
\qquad 0\le e_u\le x_u\le1.
\]
If $x_u=0$, then $e_u=0$ and these reduce to $0\le s_u\le d_u$.
If $x_u=1$, both bounds equal $2-e_u$. Signed arithmetic is intended.
The stronger formulation introduces $y_{uv}$ for each allowed edge, with
\[
0\le y_{uv},\qquad y_{uv}\le x_u,\qquad y_{uv}\le x_v,
\qquad y_{uv}\ge x_u+x_v-1.
\]
For Boolean $x$, these force $y_{uv}=x_ux_v$. Impose
$\sum_{v\sim t}y_{tv}=1$ at the root and
$\sum_{v\sim u}y_{uv}=2x_u-e_u$ elsewhere. Thus every actual odd-edge
partner gives a feasible assignment. Lean checks the signed-integer
degree and Boolean-product equivalences. The serialized finite models
have a separate exact-arithmetic audit.

\paragraph{Upper certificates.}
For inequalities $Az\le b$, equalities $Ez=f$, bounds $0\le z\le1$,
and objective $c\cdot z$, choose a positive integer $D$, nonnegative
integer weights $Y$ and signed integer weights $Z$. Set
$r=Dc-A^{\mathsf T}Y-E^{\mathsf T}Z$. Then
\[
D\,c\cdot z\le b\cdot Y+f\cdot Z+\sum_i\max(r_i,0).
\]
This follows by expanding the objective, summing the weighted rows,
and using $r_i z_i\le\max(r_i,0)$. Exact residual compensation makes
the bound independent of numerical dual feasibility or optimality.
All saved coefficients and multipliers were audited with exact integers.
Lean checks the corresponding integer-variable implication with the
coefficient expansion explicit; it does not check every saved array.

The vertex-only bounds are $108.36883$ and $107.110383$ at roots 0 and 78.
For the stronger edge formulation, the following values enclose the
maximum fractional cardinality, even after every cycle occupancy
inequality is imposed:
\[
\begin{array}{c|c|c}
\text{Root}&\text{Exact feasible cardinality}&\text{Exact upper certificate}\\\hline
0&\displaystyle\frac{43286778654}{441499285}
 &\displaystyle\frac{49022513}{500000}\\[6pt]
78&\displaystyle\frac{75253867064343}{770614508036}
 &\displaystyle\frac{3051701}{31250}
\end{array}
\]
The feasible values are approximately $98.044958$ and $97.654361$;
the upper bounds are $98.045026$ and $97.654432$.
The upper certificate at root 78 limits an actual odd-edge partner to
96 vertices, hence 95 edges, using even integral cardinality. This is
a fixed-parent statement and does not exclude the 93-edge target.

\paragraph{Why the fractional points satisfy every cycle inequality.}
For one exact rational point put $w_u=1-x_u$. For each deleted edge
$ab$, a saved rational potential $p$ satisfies
\[
p_a=0,\qquad |p_u-p_v|\le w_u+w_v\quad(uv\ne ab),
\qquad p_b+w_a+w_b\ge2.
\]
Take any simple cycle containing $ab$ and follow its remaining path
from $a$ to $b$. Summing potential differences bounds $p_b-p_a$ by
the sum of its edge costs. Adding the deleted edge counts every
cycle vertex twice, so $2\sum_{u\in C}w_u\ge2$. Consequently
\[
\sum_{u\in C}x_u\le |C|-1
\]
for every simple cycle. The exact audit checks all 337 deleted-edge
potentials at each root, including 113232 edge inequalities per root.
It also checks all 574 variable bounds and every model row.
Lean checks the telescoping and cycle-counting implication with integer
scaling; the rational data and their assembly remain independently
audited native arithmetic.

\begin{proposition}[Limitation of the continuous cycle formulation]
\label{prop:cycle-relaxation219}
For either joining endpoint of the saved 98-edge parent, the continuous
edge formulation admits a selection of exactly 94 vertices satisfying
every simple-cycle occupancy inequality.
\end{proposition}
\begin{proof}
The exact feasible cardinality $q$ in the table exceeds 94. The one-edge
paths $(0,2)$ and $(78,14)$ respectively give feasible cardinality two.
Mix the corresponding two assignments with weight $92/(q-2)$ on the
larger one. This weight lies between zero and one, and the resulting
cardinality is exactly 94. All model and cycle inequalities are linear,
so the mixture preserves them. Both resulting rational assignments
and their exact model constraints have also been audited directly.
\end{proof}
Thus adding cycle occupancy inequalities alone cannot exclude the target
in this continuous formulation. Integrality remains essential; the
fractional assignments provide no snake. No global bound changes.
The certificates and verification limits are recorded in milestone
219~\cite{research219}.

The next candidate strengthening uses arbitrary vertex subsets $U$.
An actual path induces a forest on $U$. Therefore, for each $v\in U$,
\[
\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v.
\]
If $v$ is selected, the nonempty forest has at most its vertex count
minus one edges; if $v$ is unselected, the weaker bound follows as well.
These inequalities couple all selected edges of a subset. Their effect
on the saved fractional points has not yet been computed.

'''
brief=r'''
\paragraph{Why more cycle inequalities are insufficient by themselves.}
The degree model was relaxed by allowing selection and endpoint variables
to lie between zero and one. Adding edge variables for products of
Boolean selections improves its numerical bounds substantially.
Exact certificates now place the maximum fractional cardinality between
$98.044957$ and $98.045026$ at root 0, and between
$97.654360$ and $97.654432$ at root 78.

Both lower endpoints come from saved rational assignments satisfying
every simple-cycle inequality. This was checked without enumerating
all cycles. With $w_u=1-x_u$, each deleted edge $ab$ has a potential
with $p_a=0$, $|p_u-p_v|\le w_u+w_v$ on other edges and
$p_b+w_a+w_b\ge2$. Summing along a cycle minus $ab$, then restoring
that edge, gives $2\sum_{u\in C}w_u\ge2$. Hence at least one unit
of fractional nonselection occurs on every cycle.

Mixing either assignment with the corresponding one-edge path gives
an exact feasible cardinality of 94. The mixing weight is
$92/(q-2)$ when the larger cardinality is $q>94$.
Therefore even all cycle occupancy inequalities cannot exclude the
93-edge partner target in this continuous model. These fractional
assignments establish a limitation of the method; they are not paths.
The finite rational data have independent exact audits. Lean checks
the degree encoding, integer weighted-bound argument and telescoping
cycle implication, with numerical array assembly kept separate.

A stronger candidate uses any subset $U$ and $v\in U$:
\[
\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v.
\]
This holds because the part of a path inside $U$ is a forest, with
at most one fewer edge than selected vertices when $v$ is selected.
The next calculation will determine whether these subset inequalities
exclude the saved fractional assignments or lower the bound below 94.

'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name; mirror=R/'paper'/name
    assert p.read_bytes()==mirror.read_bytes()
    backup=H/'data'/('before-'+name); assert not backup.exists(); backup.write_bytes(p.read_bytes())
    old=p.read_text(encoding='utf-8'); new=old.replace('Research state after round 218','Research state after round 219')
    if name=='snake9_research.tex':
        marker=r'\section{Verification scope and remaining problem}'
        assert new.count(marker)==1; new=new.replace(marker,main+marker)
        marker='The paper separates written proofs, checked implications, native'
        addition=('Exact fractional certificates show that the fixed-parent degree\n'
                  'formulation, even with every simple-cycle occupancy inequality,\n'
                  'cannot exclude the 94-vertex compatible-partner target.\n\n')
        assert new.count(marker)==1; new=new.replace(marker,addition+marker)
        bib=r'''
\bibitem{research219}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Exact degree relaxations and
the limitation of all cycle occupancy inequalities}. Research milestone
219, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/219-linear-partner}.

'''
        new=new.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
    else:
        marker=r'\section{What would resolve the question}'
        assert new.count(marker)==1; new=new.replace(marker,brief+marker)
        new=new.replace('milestones through round 218','milestones through round 219')
    assert re.search(r'\\author\{[^\n]*',old).group()==re.search(r'\\author\{[^\n]*',new).group()
    if name=='snake9_research.tex':
        assert re.search(r'\\hypersetup\{.*?\n\}',old,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',new,re.S).group()
    p.write_text(new,encoding='utf-8',newline='\n');mirror.write_bytes(p.read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS_219')
