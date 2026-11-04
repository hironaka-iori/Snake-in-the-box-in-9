from pathlib import Path
import hashlib,json,re
R=Path('E:/Snake-in-a-box');H=R/'milestones/166-small-loss-and-paper'
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');mirror=R/'paper/snake9_research.tex'
b=p.read_bytes();assert mirror.read_bytes()==b
assert hashlib.sha256(b).hexdigest()=='e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb'
s=b.decode().replace('\r\n','\n');preamble=s.split('\\begin{document}',1)[0]
def replace(a,c):
 global s
 assert s.count(a)==1,(a[:100],s.count(a));s=s.replace(a,c)
replace('those parameters cannot strengthen this fixed comparison. This finite-graph\nconclusion does not establish a new snake bound. The optimum and the\nnumerical conjecture 196 remain open.',r'''those parameters cannot strengthen that fixed comparison. Retaining the
exact rounding loss permits a different conditional comparison with the
$012034$ floor weakened to 17. At mean $4462/9$ and range $5411/9$, a total
loss of at least four gives $m\le235-3/42262$, hence $m\le234$.
The positive-loss premise and inherited geometric and certificate
requirements remain unresolved. Explicit disconnected configurations
have zero loss, so local degree restrictions alone cannot supply the
missing premise. The optimum and the numerical conjecture 196 remain open.''')
replace('Strengthened retained comparison & Exact finite optimum $235-15/2348$; its geometric and certificate premises remain separate.\\\\',r'''Retained finite comparisons & The earlier loss-discarding optimum is $235-15/2348$. With the $012034$ floor 17 and total loss at least four, a checked finite potential gives $235-3/42262$. The loss and geometric premises remain unresolved.\\''')
anchor='\\begin{lemma}[Weighted window packing]'
insert=r'''\subsection{The exact remainder by selected-neighbour degree}
The same identities retain the loss exactly:
\begin{equation}\label{eq:exact-loss-budget}
G_{12}+840(m+1)+\sum_q r_{12}(q)=221136.
\end{equation}
Every empty square through $q$ uses two unselected neighbour directions.
Distinct squares use distinct pairs, so
\[
e(q)\le\binom{9-d(q)}2.
\]
For $d(q)=7$ this gives $e(q)\le1$, and for $d(q)\ge8$ it gives $e(q)=0$.
Since $1,2,3,4,6$ divide 12, the remaining degree cases give
\begin{equation}\label{eq:degree-loss}
\sum_q r_{12}(q)
=12\sum_{d(q)=0}e(q)
+\sum_{d(q)=5}\bigl(2e(q)\bmod5\bigr)
+5\sum_{d(q)=7}e(q).
\end{equation}
At degree five the possible counts $e=0,1,\ldots,6$ give residues
$0,2,4,1,3,0,2$. Rounding takes place after the incident empty squares
have been counted; replacing the middle term by $2\sum_{d(q)=5}e(q)$
is invalid. For example, the induced path with vertices
$(1,3,2,6,4,12,8,24,16)$ has $d(0)=5$ and $e(0)=6$, giving
$72\bmod5=2$ rather than 12.

Consequently, total loss at most three requires $e(q)=0$ whenever
$d(q)=0$ or $7$, forbids $e(q)=2$ at degree five, and permits at most
three degree-five corners with positive residue. Degree-five corners
with five empty squares have residue zero and must remain allowed.
These restrictions follow from the nonnegativity of all summands.
The geometric counting argument is given above; its finite arithmetic
cases have a separate verification record.

'''
replace(anchor,insert+anchor)
replace('The current conditional argument requires floor 18 for $012034$ and floor 16 for the other three pending shapes.', 'The earlier conditional argument discards the remainder and requires floor 18 for $012034$ and floor 16 for the other three pending shapes. Section~\\ref{sec:retained-loss-comparison} gives an alternative using floor 17 and a separate total-loss premise.')
anchor='\\section{A finite comparison graph and its interpretation}'
insert=r'''\begin{proposition}[Potential comparison retaining the loss]\label{prop:loss-potential}
Assume $m\ge9$, the window packing premise $W+2520\le5G_{12}$, and
\[
\mu(m-8)\le W+R+24C.
\]
Then
\begin{equation}\label{eq:retained-loss-potential}
(4200+\mu)m\le1098960+8\mu+24C+R-5\sum_qr_{12}(q).
\end{equation}
\end{proposition}
\begin{proof}
Multiply~\eqref{eq:exact-loss-budget} by five and use the packing premise
to obtain $W+4200m\le1098960-5\sum_qr_{12}(q)$.
Substitute the assumed lower bound for $W$. The resulting arithmetic
implication is checked in Lean with each premise retained~\cite{loss163archive}.
\end{proof}

'''
replace(anchor,insert+anchor)
anchor='\\section{Remaining requirements for a stronger bound}'
insert=r'''\subsection{A weaker local floor with the loss retained}\label{sec:retained-loss-comparison}
Keep the retained graph and its additional count restrictions, but weaken
the $012034$ share floor from 18 to 17. All other floors and the
count-conditioned $012032$ increment remain as in the preceding profile.
A retained nine-edge cycle has weight 4462, and a retained nine-edge walk
has weight 3861; neither has a recorded occurrence event. Thus every
nonnegative mean and occurrence credit satisfy
\[
9\mu\le4462,\qquad R\ge9\mu-3861.
\]
The loss-discarding comparison is consequently at least
\[
\frac{9931745}{42262}=235+\frac{175}{42262}.
\]
This is an obstruction to that comparison; no attaining potential is
claimed by these two witnesses alone~\cite{floor158archive}.

The loss-retaining comparison behaves differently. Exact integer checks
on all 4661572 retained edges provide a potential satisfying
\[
9w(u,v)+p(u)-p(v)\ge4462,\qquad 0\le p\le5411.
\]
Its minimum edge slack is zero. A separately reconstructed 35-edge walk
has unscaled weight 16751, so every such potential has range at least
\[
35\cdot4462-9\cdot16751=5411.
\]
The exhibited range is therefore minimum at mean $4462/9$. No joint
optimality over different means is claimed.

In~\eqref{eq:retained-loss-potential}, set $\mu=4462/9$, $R=5411/9$
and $C=0$. If total loss is at least four, then
\[
m\le\frac{9931567}{42262}=235-\frac3{42262}<235,
\]
and integrality gives $m\le234$. Loss three instead gives
$235+42/42262$, so four is the least integer loss that crosses this
threshold at these parameters. These numerical implications have passed
Lean checks. The all-edge potential check is a separate exact-integer
computation, and the inherited local floors, count and parity restrictions,
reference exclusions, and interpretation for actual snakes remain
obligations~\cite{loss164archive,threshold165archive}.
To exclude a hypothetical 235-edge snake, its odd length supplies the
applicable parity premise; the other premises still require proof.

\paragraph{Tests of the missing loss premise.}
An independent enumeration of coordinate squares gives loss 163 for the
printed 191-edge witness. The 131 saved 191-edge snakes have losses from
152 to 913. These observations impose no bound on unknown longer snakes.
There are also explicit zero-loss selected sets which satisfy only part
of the path conditions. Assign two-bit parity-check columns
$(1,1,2,2,3,3,3)$ to the first seven coordinates and leave the last two
coordinates free. The kernel consists of 32 disjoint induced squares.
Removing one selected vertex leaves exactly two selected degree-one
vertices and all other selected degrees two, while its loss remains zero.
Removing one corner per square with the recorded parity-dependent choice
gives 32 disjoint three-vertex paths, also with zero loss.
The first example retains cycles; the second has 64 endpoints.
Neither is a snake or a counterexample at the target length. They show
why the omitted global path requirements cannot be inferred from the
local degree or acyclicity condition alone.

'''
replace(anchor,insert+anchor)
replace('The direct route to 234 requires a universal six-count floor, the stated',r'''The retained-loss alternative in Section~\ref{sec:retained-loss-comparison}
requires total loss at least four for the hypothetical 235-edge case,
as well as every inherited graph premise. A concrete next target is to
exclude total loss at most three under the full path conditions.
The finite zero-loss countermodels do not settle that target.
The direct route to 234 requires a universal six-count floor, the stated''')
old='''For the preserved $012034$ share-18 proof, the original-clause assignment
now transfers through all 104 chunks to the materialized initial tree and
composes with the checked 1055-deduction prefix using 6006 propagation
references. The original constructor body is unchanged. The preceding
assembly timeout is retained in Appendix~\\ref{app:historical-verification-records}.
The remaining full replay and actual-snake interpretation are unfinished.
These records establish progress on certificates without completing these
local share theorems~\\cite{bridge146archive}.'''
new=r'''For the preserved $012034$ share-18 proof, interpretation of all 13224
input clauses is complete. The accepted consequence of the original
clause set reaches 448 continuation segments in 14 groups. Including
the earlier prefix, the checked portion contains 33111 deductions and
2734960 propagation references. There remain 112104 deductions and
11975921 references. The final contradiction, coordinate interpretation
and reversal needed for the share theorem are unfinished. The historical
1055-deduction checkpoint and its earlier assembly record remain in
Appendix~\ref{app:historical-verification-records}. The current prefix
establishes no final contradiction or new local share theorem
by itself~\cite{replay165archive}.'''
replace(old,new)
refs=r'''
\bibitem{floor158archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Weaker-floor comparison obstructions}. Research record, 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/958068470c2f6f252f858b1661142d0746582d1b/milestones/158-memory-bounded-floor-test}.
\bibitem{loss163archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Retaining the exact corner-share loss}. Research record, 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/958068470c2f6f252f858b1661142d0746582d1b/milestones/163-share18-replay-continuation}.
\bibitem{loss164archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{A loss-corrected finite potential}. Research record, 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/db87226a5ab718bbe513bd12a37d194505825074/milestones/164-loss-corrected-potential}.
\bibitem{threshold165archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Exact numerical thresholds for the retained-loss comparison}. Research record, 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/958068470c2f6f252f858b1661142d0746582d1b/milestones/165-share18-continuation-and-pause}.
\bibitem{replay165archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Partial certificate replay and its verified stopping point}. Research record, 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/958068470c2f6f252f858b1661142d0746582d1b/milestones/161-share18-full-replay}.
'''
replace('\\end{thebibliography}',refs+'\n\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==preamble
out=s.replace('\n','\r\n').encode() if b'\r\n' in b else s.encode()
p.write_bytes(out);mirror.write_bytes(out)
(H/'data/paper-edit.json').write_text(json.dumps(dict(before_sha256=hashlib.sha256(b).hexdigest(),after_sha256=hashlib.sha256(out).hexdigest(),preamble_unchanged=True,authors_unchanged=True,full_source_review='review/full-paper-review.md',last_full_revision=166,next_full_revision=176,compile_pending=True),indent=2)+'\n',encoding='utf-8')
print('Updated existing editor source and identical repository mirror.')
