from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert json.loads((H/'data/coefficients-replay.json').read_bytes())['status']=='PASS'
main=(D/'snake9_research.tex').read_text(encoding='utf-8');short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
section=r'''
\subsection{Recovery after three missing neighbour counts}
\label{sec:three-erasure238}
The preceding recovery theorem extends to three missing observations.
This concerns arbitrary selected vertex sets in $Q_9$, so it can also
serve as a consistency condition during a snake construction.

\begin{proposition}
The neighbour counts at any 509 of the 512 vertices of $Q_9$ determine
a binary vertex selection uniquely. If the selected parity side is
known, any 253 of the 256 opposite-side counts suffice.
\end{proposition}
\begin{proof}
Subtract two proposed binary selections and write $z$ for their
pointwise difference. Then $z$ takes values in $\{-1,0,1\}$. Suppose its
neighbour sums vanish except possibly at distinct vertices $p,q,r$.
The inverse formula, applied at their antipodes, gives
\[
\begin{pmatrix}128&a&b\\a&128&c\\b&c&128\end{pmatrix}
\begin{pmatrix}x\\y\\w\end{pmatrix}
=315\begin{pmatrix}s\\t\\u\end{pmatrix},
\]
where $x,y,w$ are the three exceptional neighbour sums,
$a,b,c\in\{0,35,-10,8,-16\}$, and $s,t,u\in\{-1,0,1\}$.
We show that this integer system has only the zero solution.

The sole odd off-diagonal coefficient is 35. Simultaneously permuting
rows and columns allows four cases. If no coefficient is 35, parity
forces $s=t=u=0$. A row containing the largest absolute unknown $M$
then gives $128M\le32M$, hence $M=0$.

If exactly one coefficient is 35, take $a=35$ and put
$M=\max(|x|,|y|)$. The third equation has even left side, so $u=0$ and
$128|w|\le32M$. A row attaining $M$ gives
$128M\le315+35M+16|w|$, hence $89M\le315$.
Thus $M\le3$ and $w=0$. Subtraction of the first two equations yields
$31(x-y)=105(s-t)$. Coprimality and $|s-t|\le2$ force $s=t$ and $x=y$.
The remaining equation $163x=315s$ forces $s=x=y=0$.

If exactly two coefficients are 35, take $a=b=35$.
Subtracting the last two equations gives
$(128-c)(y-w)=315(t-u)$. The four possible values of $128-c$ are
128, 138, 120 and 144; none divides 315 or 630. Hence $t=u$ and $y=w$.
Eliminating $x$ now gives
\[
D y=315(128t-35s),\qquad D=128(128+c)-2450.
\]
For $c=0,-10,8,-16$, respectively, $D/\gcd(D,315)$ is
13934, 1406, 1662 or 566. Each divides $128t-35s$, whose absolute
value is at most 163. Therefore $128t=35s$, forcing $s=t=0$ and all
unknowns zero. Finally, if all three coefficients are 35, row
subtraction forces equal unknowns and equal right-hand sides; the
remaining equation is $22x=35s$, which again forces zero.

All exceptional neighbour sums therefore vanish. The inverse gives
$z=0$ at every vertex. For the parity specialization, the 256 counts
on the selected side are automatically zero, leaving at most three
unknown observations on the other side.
\end{proof}

The actual-cube recovery statement and binary-selection corollary have
passed kernel checking. The checked arithmetic version retains the
automatic bounds $-9\le x,y,w\le9$ and treats the finite coefficient
cases by exact elimination. The written argument above proves the
stronger arithmetic statement without those bounds. It also explains
why the calculation succeeds~\cite{research238}.

No connectedness conclusion follows from these counts. A proposed
count profile must still correspond to a binary selection and to a
connected induced path. The theorem shows that two distinct selections
must differ in their neighbour counts at at least four positions.
A one-vertex change alters nine counts, so the smallest possible
number of altered counts remains between four and nine. The next
question is whether four missing observations can also be tolerated.

'''
small=r'''
\section{Three missing observations can also be recovered}
The recovery result now tolerates three missing counts: any 509 of the
512 neighbour counts determine the selected set. When one parity side
is known in advance, 253 of the 256 opposite-side counts suffice.

For the reasoning, compare two selections with the same observed
counts. Their selection difference is always $-1$, zero or one, and
their count difference is confined to three positions. Apply the inverse
formula at the three antipodes. This gives three integer equations with
diagonal coefficient 128 and off-diagonal coefficients among
$0,35,-10,8,-16$. The right sides are $-315$, zero or 315.
Parity and divisibility rule out every nonzero solution: the proof
separates the cases according to how many off-diagonal coefficients are
the odd number 35. Thus all three missing count differences vanish,
and the inverse makes the selections equal.

This result and its connection to the actual cube passed Lean.
The main paper includes the short mathematical argument; the archive
also contains the exact coefficient calculations~\cite{research238}.
It supplies a necessary consistency condition for proposed constructions.
It does not decide whether a selection is one connected snake.
Two distinct selections must differ in at least four neighbour counts.
Whether four missing counts are also recoverable is the next question.
No longer snake or new global bound was obtained in this round.

'''
bib=r'''\bibitem{research238}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Recovery from three missing neighbour
counts}. Research milestone 238, 18 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/238-three-count-recovery}.

'''
for name,s,marker,addition in [('snake9_research.tex',main,r'\section{A numerical conjecture and its limitations}',section),('snake9_frontier_explanation.tex',short,r'\section{Remaining questions}',small)]:
 assert s.count(marker)==1 and 'research238' not in s
 s=s.replace(marker,addition+marker).replace('Research state after round 237','Research state after round 238').replace('milestones through round 237','milestones through round 238')
 s=s.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
 (D/name).write_text(s,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes((D/name).read_bytes())
 print('UPDATED',name)
