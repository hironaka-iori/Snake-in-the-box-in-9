from pathlib import Path
import re,hashlib
r=Path('E:/Snake-in-a-box');h=r/'milestones/176-boundary-retuning';p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
s=p.read_text(encoding='utf-8');assert p.read_bytes()==(r/'paper/snake9_research.tex').read_bytes();before=s;prefix=s.split('\\begin{document}')[0]
def once(a,b):
 global s
 assert s.count(a)==1,(a[:70],s.count(a));s=s.replace(a,b)
a=s.index('The conditional comparison giving 234 still requires');b=s.index('\n\\end{abstract}',a)
s=s[:a]+r'''A new boundary argument gives sums at least fourteen and sixteen for
six and seven consecutive internal counts. Together with the endpoint
bounds, these improve the omitted contributions in the two finite-graph
arguments. The archived count-only argument now yields
$39m+2s_0\le9192$, so a hypothetical 235-edge snake has at most thirteen
empty squares. In the share argument, the boundary contribution rises
from twenty-one to twenty-four. The existing potential with mean
$4462/9$ and range $5411/9$ then gives the conditional bound
$m\le235-3063/42262$, without a positive-loss assumption.
The physical share-loss identity, the new boundary counts and their
actual-snake accounting have passed Lean checks. The finite potential
and its local-share, count-restriction and graph-coverage premises remain
separate obligations. Retuning under weaker share floors is described
below. No new unconditional numerical length bound is claimed; the
optimum and the numerical conjecture 196 remain open.
'''+s[b:]
once('The proof begins with the square census and the archived six-centre argument\nfor 235.', 'The proof begins with the square census and the archived six-centre argument\nfor 235. The new six-count boundary strengthens its retained empty-square\ninequality, while the seven-count boundary strengthens the share argument\nwithout requiring a positive lower bound on rounding loss.')
once('Conditional bound 234 & Slope 496, range 602 and boundary contribution 21. Four local shares remain unresolved; the $012032$ share-16 premise is established. The remaining 1358 reference refutations and complete finite potential certificate are still required.', 'Conditional bound 234 & The new boundary contribution 24 removes the positive-loss premise from the retained floor-17 comparison. Local shares, reference exclusions, count restrictions and the complete graph certificate remain separate obligations.')
once('Retained finite comparisons & The earlier loss-discarding optimum is $235-15/2348$. With the $012034$ floor 17 and total loss at least four, a checked finite potential gives $235-3/42262$. The loss and geometric premises remain unresolved.', 'Boundary and retained comparisons & Six and seven omitted internal counts contribute at least 14 and 16. The former gives $s_0\le13$ at length 235 using the archived walk; the latter gives conditional 234 with nonnegative loss.')
# Place a proof of the shared local arithmetic before either application.
anchor=r'\subsection{Reading a singleton count from missing corners}'
insert=r'''\subsection{Short sums needed at the boundary}
\begin{lemma}[Six and seven internal counts]\label{lem:boundary-short-sums}
Any six consecutive internal singleton counts sum to at least fourteen;
any seven sum to at least sixteen.
\end{lemma}
\begin{proof}
The counts are positive. Theorems~\ref{thm:no-adjacent-one-three} and
\ref{thm:no-three-twos} establish that a count one has internal neighbours
at least four, and three consecutive counts cannot all equal two.
Every adjacent pair therefore sums to at least four. Every triple sums
to at least six, with equality possible only for $(1,4,1)$: if no count
is one, all three are at least two and equality is excluded; if a count
is one, its neighbour restrictions give the stated case.

Four consecutive counts sum to at least nine. Otherwise both disjoint
pairs would sum to four, which forces all four counts to equal two and
contradicts the triple restriction. Split six counts into two triples.
If both sums exceed six, their total is at least fourteen. If one triple
is $(1,4,1)$, the adjacent count in the other triple is at least four,
and the remaining pair sums to at least four, again giving fourteen.
For seven counts, split into four followed by three. Unless the last
triple is $(1,4,1)$, the total is at least $9+7=16$. In that exceptional
case, the preceding count is at least four and the first triple contributes
at least six, so the total is at least $6+4+6=16$.
\end{proof}
The numerical bounds are sharp under these count restrictions alone:
$(2,2,3,2,2,3)$ and $(2,2,3,2,2,3,2)$ attain them. No snake realizing
these tuples at a minimal boundary is asserted. The arithmetic and its
application to actual snake prefixes have passed Lean checks.

'''
once(anchor,insert+anchor)
# Strengthen the count-only argument, retaining the archived walk premise.
a=s.index(r'\begin{proposition}[Singleton estimate with boundary terms]');b=s.index('\nThe following sections retain the empty-square term',a)
s=s[:a]+r'''\begin{proposition}[Singleton estimate with boundary terms]\label{prop:count-235}
Every nontrivial $m$-edge snake in $\Q_9$ satisfies
\begin{equation}\label{eq:count-235}
4m\le T+13.
\end{equation}
\end{proposition}
\begin{proof}
For $m\ge7$, the archived six-centre state walk appends counts
$b_7,\ldots,b_{m-1}$ and has $m-7$ transitions. Summing
\eqref{eq:six-centre-step} and using the potential range seven gives
\[
4(m-7)\le\sum_{j=7}^{m-1}b_j+7.
\]
Lemma~\ref{lem:boundary-short-sums} gives at least fourteen from the
first six internal counts, and the endpoints contribute at least eight.
Since $b_j\le\alpha_j$, the sum on the right is at most $T-22$.
Thus $4m-28\le T-15$, proving the assertion. For $1\le m<7$,
positivity and the endpoint bounds give $T\ge m+7$ and $4m\le T+13$.
The new boundary and this deduction are Lean-checked under the stated
archived walk premise; its complete independent rebuild remains pending.
\end{proof}

\begin{theorem}[Retained empty-square bound]\label{thm:upper235}
Every nontrivial $m$-edge snake in $\Q_9$ satisfies
\begin{equation}\label{eq:retained-empty-235}
\boxed{39m+2s_0\le9192.}
\end{equation}
In particular, $m\le235$.
\end{theorem}
\begin{proof}
Substitute $T\ge4m-13$ into $T+2s_0+35(m+1)=9214$.
This gives $39m+2s_0\le9192$. Since $39\cdot236=9204>9192$,
integrality gives $m\le235$. The zero-edge path satisfies the length
bound directly. Together with Theorem~\ref{thm:lower}, this proves
Theorem~\ref{thm:main}, with the archived-proof qualification already stated.
\end{proof}

\begin{corollary}[Fourteen-empty-square target]\label{cor:eighteen-empty}\label{cor:fourteen-empty}
A snake with at least fourteen empty squares has at most 234 edges.
In particular, a hypothetical 235-edge snake has $s_0\le13$.
\end{corollary}
\begin{proof}
For $m\ge235$, inequality~\eqref{eq:retained-empty-235} gives
$2s_0\le9192-39\cdot235=27$, so $s_0\le13$.
Conversely, $s_0\ge14$ gives $39m\le9164<39\cdot235$.
The count and census implications have passed Lean under their stated
premises. This improves the former target of eighteen empty squares;
the numerical length upper bound remains 235.
\end{proof}
'''+s[b:]
once('The new remainder-sum representation still needs an explicit identification\nwith the earlier implementation of the global share budget before these\ncertificates are combined in a single Lean derivation.', 'The physical empty-square and neighbour counts now have checked\nidentifications with the earlier share-budget quantities. The exact\nshare-plus-loss identity and the resulting budget inequality are checked\nin the same Lean derivation.')
once(r'\paragraph{The remaining critical case after rounds 172--174.}',r'\paragraph{The small-loss reduction with the earlier boundary.}')
a=s.index('The finite-list support bound, the complete positive-remainder list,');b=s.index(r'\begin{lemma}[Weighted window packing]',a)
s=s[:a]+r'''The finite-list classification and modular deductions have passed Lean.
The actual-snake support bound, divisibility restriction and conditional
length reduction are now checked with the physical loss and global budget.
These conclusions describe the earlier boundary-21 argument. The stronger
boundary-24 argument below excludes length 235 under the same potential
premise without any separate lower bound on $L$. The local share and graph
premises remain unresolved; consequently this does not exclude a
235-edge snake unconditionally.

'''+s[b:]
once('Section~\\ref{sec:retained-loss-comparison} gives an alternative using floor 17 and a separate total-loss premise.', 'Section~\\ref{sec:retained-loss-comparison} records the earlier floor-17 argument with a loss premise. The stronger boundary in Proposition~\\ref{prop:boundary24} removes that loss requirement, and Section~\\ref{sec:boundary-retuning} considers weaker floors.')
once(r'\subsection{The strengthened boundary estimate}\label{sec:boundary21}',r'\subsection{Boundary contributions of twenty-one and twenty-four}\label{sec:boundary21}')
anchor=r'\begin{corollary}[Potential criterion for excluding 235]'
insert=r'''\begin{proposition}[Boundary contribution of twenty-four]\label{prop:boundary24}
With the notation and local share premises of Proposition~\ref{prop:boundary21},
\[
\boxed{W+2880\le5G_{12},\qquad W+4200m+5L\le1098600,}
\]
where $L=\sum_qr_{12}(q)$.
\end{proposition}
\begin{proof}
The omitted singleton positions are $0,1,\ldots,7,m$. The seven internal
counts sum to at least sixteen by Lemma~\ref{lem:boundary-short-sums};
the two endpoints contribute at least eight. Thus
$\sum_{j=8}^{m-1}b_j+24\le T$.
Each selected share is counted by at most five windows, so the first
inequality follows after multiplying the count inequality by 120.
Combining it with $5G_{12}+4200(m+1)+5L\le1105680$ gives the second.
The actual counts, share reindexing and indexed window capacity have all
passed Lean checks; each local lower bound remains an explicit premise.
\end{proof}
Consequently, whenever $\mu(m-8)\le W+R$, the stronger comparison is
\begin{equation}\label{eq:boundary24-comparison}
\boxed{(4200+\mu)m+5L\le1098600+8\mu+R.}
\end{equation}
At the previously checked parameters $\mu=4462/9$ and $R=5411/9$,
this gives
\[
42262m+45L\le9928507,
\qquad m\le235-\frac{3063}{42262}<235.
\]
Thus $m\le234$ using only $L\ge0$. This actual-snake implication has
passed Lean under its local-share and potential premises. The old
boundary-21 comparisons remain valid as weaker historical comparisons.

'''
once(anchor,insert+anchor)
once('Keep the retained graph and its additional count restrictions, but weaken', 'The following records the boundary-21 comparison used before the improvement\nin Proposition~\\ref{prop:boundary24}. Keep the retained graph and its additional count restrictions, but weaken')
once(r'\paragraph{Tests of the missing loss premise.}',r'\paragraph{Tests of the former positive-loss target.}')
a=s.index('The retained-loss alternative in Section~\\ref{sec:retained-loss-comparison}\nrequires total loss');b=s.index('The direct route to 234 requires',a)
s=s[:a]+r'''The boundary-24 argument removes the additional positive-loss requirement
from the retained finite comparison. The principal remaining work is to
establish the weakened local share floors and every retained graph
assumption. Small-loss geometry remains useful information about snakes,
but proving $L\ge4$ is no longer necessary for this conditional route.
The strengthened count-only argument also reduces the sufficient
empty-square target from eighteen to fourteen.
'''+s[b:]
# Distinguish the older accepted-key profile from the current retained-graph route.
once('\\item For 234, complete the remaining local shares', '\\item For the earlier accepted-key profile giving 234, complete the remaining local shares')
once('The conditional 234 profile uses share floors', 'The earlier accepted-key conditional 234 profile uses share floors')
# Mark the profile-specific optimisation limits; changing the boundary escapes them.
once('A further improvement must alter at least one witness or the comparison\nitself.', 'A further improvement must alter at least one witness or the comparison\nitself. Proposition~\\ref{prop:boundary24} changes the boundary constant and\ntherefore lies outside this earlier optimisation statement.')
assert s.split('\\begin{document}')[0]==prefix
p.write_text(s,encoding='utf-8');(r/'paper/snake9_research.tex').write_bytes(p.read_bytes())
(h/'review/main-revision-stage1.json').write_text(__import__('json').dumps({'before_sha256':hashlib.sha256(before.encode()).hexdigest(),'after_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'preamble_unchanged':True,'scope':'Current abstract, proof overview, retained count inequality, loss integration, boundary24 and remaining requirements; historical finite comparisons preserved.'},indent=2)+'\n')
print('Updated main manuscript in place',len(s.splitlines()),'lines')
