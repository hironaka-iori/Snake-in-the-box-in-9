from pathlib import Path
r=Path('E:/Snake-in-a-box');p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');s=p.read_text(encoding='utf-8')
anchor=r'\section{Remaining requirements for a stronger bound}'
insert=r'''\subsection{Retuning after the stronger boundary}\label{sec:boundary-retuning}
All comparisons in this subsection use boundary twenty-four, zero
occurrence credit and only the nonnegativity of the total loss. They
retain the same 4661572 edges, the additional count restrictions, and the
proved count-conditioned $012032$ increment. In particular, the hypothetical
six-count floor 25 for $0123104$, its specified first-count condition,
remaining reference exclusions and graph interpretation are still separate
premises. Lowering a share floor does not establish any of these premises.

The following two weaker profiles are sufficient for the finite comparison.
The four displayed floors are for $012034,012301,012340,012345$, respectively;
the completed floors on all other shapes remain unchanged.
\[
\begin{array}{c|c|c|c}
\text{pending floors}&\mu&R&\text{length comparison}\\\hline
(16,15,15,15)&4453/9&5411/9&235-1020/42253\\
(15,16,16,16)&4454/9&5374/9&235-642/21127
\end{array}
\]
Both rows give $m\le234$ under the local and global premises.
For the first row, lowering each applicable floor by at most one lowers
each edge weight by at most one, even when the weight uses a maximum
with an inherited lower bound. Thus the old potential satisfies
$9w'(u,v)+p(u)-p(v)\ge4453$ at the same range 5411.
Exact reweighting and a fresh scan check this on every retained edge.
For the second row, a new potential satisfies
\[
9w(u,v)+p(u)-p(v)\ge4454,\qquad 0\le p\le5374
\]
on every retained edge. Substitution into
\eqref{eq:boundary24-comparison} gives
$42254m+45L\le9928406$. These finite edge scans use exact integer
arithmetic. Lean checks the transfer and numerical implications;
a complete Lean certificate for every retained edge remains unfinished.

\begin{proposition}[Least floor and optimal comparison in the fixed profile]
\label{prop:floor15-optimum}
Keep the other pending floors at sixteen, the retained graph unchanged,
and use the boundary-24 comparison with zero occurrence credit and no
positive-loss premise. The least sufficient integer floor on $012034$
is fifteen. At that floor, the least comparison over nonnegative rational
means and ranges is
\[
\frac{4964203}{21127}=235-\frac{642}{21127},
\]
attained at $\mu=4454/9$ and $R=5374/9$.
\end{proposition}
\begin{proof}
At floor fifteen, a retained nine-edge cycle has weight 4454 and a
retained eight-edge walk has weight 3362. Hence every feasible mean and
range satisfy
\[
9\mu\le4454,\qquad R\ge8\mu-3362.
\]
The comparison is therefore at least
\[
\frac{1095238+16\mu}{4200+\mu}
\ge\frac{4964203}{21127}.
\]
The middle expression decreases with $\mu\ge0$, so its minimum under
the cycle bound is attained at $4454/9$. Equality also requires
$R=5374/9$. The exhibited potential attains both values. Its range is
independently forced by the eight-edge walk since
$8\cdot4454-9\cdot3362=5374$.

At floor fourteen, the same nine-edge cycle has weight 4448, and a
retained nine-edge walk has weight 3858. Thus
$9\mu\le4448$ and $R\ge9\mu-3858$, yielding
\[
\frac{1098600+8\mu+R}{4200+\mu}
\ge\frac{1094742+17\mu}{4200+\mu}
\ge235+\frac7{21124}>235.
\]
Lower floors cannot improve this obstruction because they only decrease
edge weights. The concrete cycle and walks were reconstructed independently
from the original source rows; their weights, retention and consecutive
endpoints were checked. The common-denominator inequalities and equality
conditions have passed Lean. This is a limitation of the specified finite
comparison, and it can change with additional loss information, different
boundary information or justified graph changes.
\end{proof}
Trials at incorrectly high means for floors twelve through fifteen were
retained as failed or unresolved trials. A long walk from one such trial
exposed the decisive nine-edge cycle and led to the corrected floor-fifteen
mean. No solver failure is used as an impossibility proof.

'''
assert s.count(anchor)==1;s=s.replace(anchor,insert+anchor)
s=s.replace('Retuning under weaker share floors is described\nbelow.', 'Retuning lowers the $012034$ floor to fifteen with the other pending\nfloors fixed. A cycle-and-walk argument proves this integer threshold\nis least for the specified comparison. A second sufficient profile\nlowers all four pending floors simultaneously to $(16,15,15,15)$.')
p.write_text(s,encoding='utf-8');(r/'paper/snake9_research.tex').write_bytes(p.read_bytes())
# Keep the short document preamble and author line, replacing its exposition.
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex');old=p.read_text(encoding='utf-8');prefix=old.split('\\begin{document}')[0];prefix=prefix.replace('Research state after round 174: 5 November 2026','Research state after rounds 175--176: 5 November 2026')
body=r'''\begin{document}
\maketitle

\textbf{Problem and present result.}
A snake in $Q_9$ is an induced path: two selected vertices are adjacent
exactly when they are consecutive on the path. Its length $m$ counts
edges. A verified construction has 191 edges. The project retains an
archived contributor proof of the upper bound 235, whose complete
independent rebuild remains pending. The maximum is unresolved.
The numerical prediction 196 has neither a construction nor an optimality
proof. The current advance strengthens the boundary accounting and reduces
the local premises needed for a conditional upper bound of 234.

\textbf{1. The exact square budget.}
Write $v=m+1$, let $T$ count coordinate squares with exactly one selected
corner, and let $s_0$ count empty squares. There are
$\binom92 2^7=4608$ coordinate squares, and each vertex lies in 36 of them.
A snake contains no fully selected square. Its three-selected-corner
squares correspond exactly to its $v-2$ internal vertices. Counting
squares and selected corner incidences therefore gives
\[
\boxed{T+2s_0+35(m+1)=9214.}
\]
This identity converts a lower count estimate into an upper length estimate.

Let $\alpha_i$ be the singleton-square count at the $i$th path vertex.
Every count is positive, the endpoint counts are at least four, an internal
count one has internal neighbours at least four, and three consecutive
internal counts cannot all equal two. These are established geometric
results. They imply that six internal counts sum to at least fourteen and
seven sum to at least sixteen.

Here is the short deduction. Every adjacent pair sums to at least four.
A triple sums to at least six, with equality only at $(1,4,1)$; four
counts sum to at least nine, since two pairs each summing to four would
force four twos. Split six counts into two triples. If one has sum six,
its adjacent count in the other triple is at least four and the remaining
pair contributes at least four. Otherwise both triples sum to at least
seven. For seven counts, split into four and three. The ordinary case
contributes at least $9+7$; a final $(1,4,1)$ forces at least $6+4+6$.
These deductions and their application to actual snake prefixes pass Lean.

The archived count-only potential gives
$4(m-7)\le\sum_{j=7}^{m-1}\min\{6,\alpha_j\}+7$ for $m\ge7$.
The six omitted internal counts and the endpoints now contribute at
least $14+8=22$, yielding $T\ge4m-13$. Shorter nontrivial paths satisfy
this estimate directly. Substitution into the square identity gives
\[
\boxed{39m+2s_0\le9192.}
\]
Thus $m\le235$, and $m=235$ requires $s_0\le13$. Proving fourteen empty
squares in that case would suffice to reach 234; the earlier target was
eighteen. This deduction uses the archived walk estimate. Its new boundary
and arithmetic are checked; the archive's full independent rebuild is
still pending. Seven disjoint share-96 windows, or 33 such windows with
distinct starts allowing overlap, would also force fourteen empty squares.
Their required occurrence frequencies remain unproved.

\textbf{2. Retaining the empty-square contribution exactly.}
For a cube vertex $q$, let $e(q)$ count incident empty squares and $d(q)$
count selected neighbours. Each selected vertex $x$ receives the integer share
\[
\sigma_{12}(x)=\sum_{q\sim x}\left\lfloor\frac{12e(q)}{d(q)}\right\rfloor.
\]
Every denominator here is positive because $x$ is selected. Define the
remainder at $q$ to be $12e(q)\bmod d(q)$ for $d(q)>0$, and $12e(q)$
otherwise; let $L$ be their sum. Exactly $d(q)$ selected vertices receive
$q$'s share, and the division algorithm recovers $12e(q)$ after the
remainder is added. Each empty square has four corners, so
\[
\sum_{x\in S}\sigma_{12}(x)+L=48s_0.
\]
Writing $G=24T+\sum_{x\in S}\sigma_{12}(x)$ and multiplying the square
identity by 24 gives
\[
\boxed{G+840(m+1)+L=221136.}
\]
The physical counts, exact share-plus-loss identity and sufficient budget
inequality are now connected in one checked Lean proof.

\textbf{3. The stronger boundary is the decisive change.}
The nine-transition model charges $120\min\{6,\alpha_{r+8}\}$ and a
valid lower bound on the five shares at positions $r+4,\ldots,r+8$.
Let $W$ be the sum over all $m-8$ windows. The omitted singleton positions
are $0,1,\ldots,7,m$. Their counts sum to at least $16+8=24$.
Each share appears in at most five windows. Consequently,
\[
W+2880\le5G,\qquad W+4200m+5L\le1098600.
\]
The earlier proof used only 21 omitted counts. The new estimate is checked
for actual snakes, with each local share lower bound retained as a premise.

If every traced edge satisfies
$w(u,v)+p(u)-p(v)\ge\mu$ and the potential range is at most $R$,
summing cancels intermediate potential values and yields
$\mu(m-8)\le W+R$. Combining the inequalities gives
\[
\boxed{(4200+\mu)m+5L\le1098600+8\mu+R.}
\]
The old potential $\mu=4462/9$, $R=5411/9$ therefore already implies
$m\le235-3063/42262<235$ using only $L\ge0$.
A separate proof of $L\ge4$ is no longer needed for this conditional route.

\textbf{4. Weaker local floors and an exact limit of this comparison.}
The finite retained graph has 4,661,572 edges. Fresh integer scans give
these sufficient profiles, listing the pending floors for
$012034,012301,012340,012345$ in that order:
\[
\begin{array}{c|c|c|c}
\text{floors}&\mu&R&\text{comparison}\\\hline
(16,15,15,15)&4453/9&5411/9&235-1020/42253\\
(15,16,16,16)&4454/9&5374/9&235-642/21127
\end{array}
\]
Each comparison is strictly below 235 and gives the integer bound 234
if the local and graph premises apply. The first follows by lowering each
edge weight by at most one. The second uses a newly computed potential.
All retained edge inequalities were checked with exact integer arithmetic;
Lean checks the arithmetic implications separately.

For the second profile, a nine-edge cycle has weight 4454 and an eight-edge
walk has weight 3362. They force $9\mu\le4454$ and
$R\ge8\mu-3362$. Substitution shows that the displayed comparison is
minimum over nonnegative rational means and ranges, at zero occurrence
credit. The exhibited potential attains it. If the $012034$ floor is
lowered to fourteen while the other floors stay sixteen, a cycle of
weight 4448 and a nine-edge walk of weight 3858 instead force every such
comparison to be at least $235+7/21124$. Thus fifteen is the least
integer floor that works in this specified family. This does not assert
that the true local share minimum is fifteen, or that a different graph,
boundary argument or positive-loss estimate cannot improve the result.

\textbf{5. What is proved, and what remains.}
The local count exclusions, new boundary counts, physical loss identity,
share packing and conditional arithmetic are Lean-checked. The actual-cube
empty-square argument also proves that an undominated vertex contributes
at least 96 to $L$: its missing-pair graph is connected, with at least
eight edges, or consists of two complete components, which have even more.
Thus $L\le95$ forces domination. The earlier $L\le3$ reduction and sparse
positive-remainder restrictions are checked, although they are unnecessary
for the stronger conditional comparison above.

The numerical upper bound 234 remains conditional. Required local share
floors, retained count restrictions, reference exclusions and the complete
graph-to-snake certificate must still be established. In particular, the
retained model includes a hypothetical six-count floor 25 on $0123104$
under its specified count conditions. A finite graph computation cannot
prove that every snake traces that graph. The partial local share replay
still checks only 33,111 of 145,215 deductions and establishes no final
contradiction. Neither a longer construction nor a proof of 196 was obtained.

The immediate continuation should establish the weakest sufficient local
profile and the remaining graph premises. The new six-count boundary also
supports the independent target $s_0\ge14$ at length 235. Research pauses
after these two rounds as requested; the records preserve the successful
certificates, unsuccessful parameter trials and exact remaining assumptions.

\smallskip
{\small Full proofs and evidence are in the companion manuscript
\texttt{snake9\_research.tex} and research records 175--176.}
\end{document}
'''
p.write_text(prefix+body,encoding='utf-8');(r/'paper/snake9_frontier_explanation.tex').write_bytes(p.read_bytes())
print('Updated both manuscripts')
