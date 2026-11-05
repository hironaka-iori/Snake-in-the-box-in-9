from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
main=r'''\subsection{Floor fourteen and the exact loss threshold}
\label{sec:floor14-loss}
The least-floor statement in Proposition~\ref{prop:floor15-optimum}
uses only $L\ge0$. Positive loss permits weaker local shares.
Keep the same retained graph, count restrictions, completed floors,
count-conditioned increment and interpretation premises. Exact potentials
now give the following two profiles; the entries refer to
$012034,012301,012340,012345$, respectively:
\[
\begin{array}{c|c|c|c}
\text{pending floors}&9\mu&9R&\text{resulting inequality}\\\hline
(14,16,16,16)&4448&5346&42248m+45L\le9928330\\
(14,14,14,14)&4448&5380&42248m+45L\le9928364
\end{array}
\]
Every potential inequality was checked on all 4661572 retained edges.
These improve the preceding reused-potential sufficient loss thresholds
of seventeen and twenty-three to two for both profiles.

\begin{proposition}[Floor fourteen with loss at least two]
Under the retained local and graph premises, uniform pending floor
fourteen and $L\ge2$ imply $m\le234$. A hypothetical path with
$m\ge235$ satisfying these premises has $m=235$ and $L\in\{0,1\}$.
\end{proposition}
\begin{proof}
The uniform potential gives $4448(m-8)\le9W+5380$.
Combine it with $W+4200m+5L\le1098600$ to obtain the second
inequality in the table. At $m=235$ it requires $45L\le84$,
so $L\le1$. At $m\ge236$ the inequality is impossible even when
$L=0$. With $L\ge2$, the length comparison is
\[
m\le235-\frac6{42248}<235.
\]
The first profile similarly requires $45L\le50$ at length 235 and
gives $m\le235-40/42248$ when $L\ge2$.
\end{proof}

\begin{proposition}[Optimality of the sufficient integer loss]
In either fixed profile above, using boundary twenty-four, zero
occurrence credit and a scalar lower bound on $L$, two is the least
sufficient nonnegative integer loss threshold obtainable by varying
the nonnegative rational potential mean and range.
\end{proposition}
\begin{proof}
A common retained nine-edge cycle has weight 4448, so $9\mu\le4448$.
For $(14,16,16,16)$ a retained nine-edge walk has weight 3854;
for the uniform profile an eight-edge walk has weight 3356.
They force $R\ge9\mu-3854$ and $R\ge8\mu-3356$, respectively.
With $L=1$, the comparison is
\[
\frac{1098595+8\mu+R}{4200+\mu}.
\]
Substituting the respective walk bound gives
$(1094741+17\mu)/(4200+\mu)$ or
$(1095239+16\mu)/(4200+\mu)$. Each expression decreases for
$\mu\ge0$. The cycle bound therefore gives the respective minima
\[
235+\frac5{42248},\qquad 235+\frac{39}{42248}.
\]
Both exceed 235. The displayed potentials attain the mean and range
bounds, and loss two suffices by the preceding proposition. Loss zero
cannot improve the comparison. This proves the stated optimality.
\end{proof}

The cycle and walk weights were reconstructed separately from the original
source rows. Lean checks the comparison, critical-case reduction and
common-denominator optimality inequalities. The finite potential scans
and the universal graph-to-snake interpretation remain different proof
obligations; the latter is still incomplete. No new unconditional length
bound follows from this optimization.

The remaining geometric cases have a precise local description.
Since $L\le1<96$, every cube vertex has a selected neighbour. If $L=0$,
all corner remainders vanish. If $L=1$, exactly one corner has remainder
one and all others have remainder zero. Every empty square at a corner
uses two of its $9-d$ unselected neighbours, so
$e\le\binom{9-d}{2}$. Under $1\le d\le9$ and $0\le e\le36$,
this bound and $12e\bmod d=1$ force $d=5$ and $e=3$.
The finite arithmetic classification passes Lean; the geometric
count bound is the direct pair-counting argument just given.
This identifies the possible exceptional corner, without excluding it.

A useful next local target is to exploit this restricted rounding loss.
For a set $C$ of selected window centres, let $k(q)$ count its neighbours
in $C$. Double counting the rational shares gives
\[
\sum_{x\in C}\sigma_{12}(x)
=\sum_{q:d(q)>0}\frac{12e(q)k(q)}{d(q)}
-\sum_{q:d(q)>0}\frac{r(q)k(q)}{d(q)},
\qquad
0\le\sum_{q:d(q)>0}\frac{r(q)k(q)}{d(q)}\le L,
\]
because $0\le k(q)\le d(q)$. Thus a rational-share lower bound of
sixteen would imply integer share at least fifteen when $L\le1$.
Establishing that rational lower bound on the required windows is a
proposed continuation, not a result of the present computation.

'''
short=r'''\textbf{5. Floor fourteen and the two remaining loss cases.}
New potentials improve the earlier sufficient loss thresholds. Under
the same retained graph and count premises, they give
\[
\begin{array}{c|c|c|c}
\text{floors}&9\mu&9R&\text{inequality}\\\hline
(14,16,16,16)&4448&5346&42248m+45L\le9928330\\
(14,14,14,14)&4448&5380&42248m+45L\le9928364
\end{array}
\]
Every inequality on the 4,661,572 retained graph edges passed an exact
integer scan. At $m=235$, even the weaker second row forces
$45L\le84$, hence $L\le1$. Thus uniform floor fourteen and $L\ge2$
suffice for the conditional upper bound 234. The remaining hypothetical
case has exactly 235 edges and $L=0$ or $L=1$.

Two is the least sufficient integer loss threshold for these fixed
comparisons. A nine-edge cycle of weight 4448 forces $9\mu\le4448$.
A nine-edge walk of weight 3854 in the first profile, and an eight-edge
walk of weight 3356 in the second, force the respective range bounds.
With $L=1$, minimizing the resulting expressions over allowed means
still gives $235+5/42248$ and $235+39/42248$. Both exceed 235;
the new potentials attain those minima. Changing the mean and range
alone therefore cannot make one unit of loss sufficient. Lean checks
these deductions, while scalar reconstruction checks the witness rows.

Both remaining loss cases dominate the cube. At $L=0$ every corner
remainder vanishes. At $L=1$, exactly one is positive; it must have
five selected neighbours and three incident empty squares. Indeed,
$e\le\binom{9-d}{2}$, and the finite possibilities with
$12e\bmod d=1$ give only $(d,e)=(5,3)$. This arithmetic is Lean-checked.
Neither remaining case has been excluded.

For the next local proof, the rational share of a window exceeds its
integer share by at most $L$: each corner's remainder is counted with
a factor between zero and one. A rational-share lower bound of sixteen
would therefore imply integer share at least fifteen when $L\le1$.
That local rational lower bound is a proposed target and remains unproved.

'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name;mirror=R/'paper'/name;assert p.read_bytes()==mirror.read_bytes()
    (H/'data'/(name+'.before.txt')).write_bytes(p.read_bytes())
    s=p.read_text(encoding='utf-8')
    if name=='snake9_research.tex':
        a=s.index('\\subsection{Trading a weaker share floor against positive loss}')
        b=s.index('\\section{Remaining requirements for a stronger bound}',a)
        s=s[:a]+main+s[b:]
    else:
        s=s.replace('Research state after round 177: 5 November 2026','Research state after round 178: 6 November 2026')
        a=s.index('\\textbf{5. A weaker floor when the loss is positive.}')
        b=s.index('\\textbf{6. What is proved, and what remains.}',a)
        s=s[:a]+short+s[b:]
        s=s.replace('after round 177 as requested','after round 178 as requested').replace('research records 175--177.','research records 175--178.')
    p.write_text(s,encoding='utf-8',newline='');mirror.write_bytes(p.read_bytes())
print('Updated existing manuscript and explanation for round178')
