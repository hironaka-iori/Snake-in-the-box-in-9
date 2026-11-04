from pathlib import Path
import hashlib,json
R=Path('E:/Snake-in-a-box');H=R/'milestones/167-undominated-corners';p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');mirror=R/'paper/snake9_research.tex'
b=p.read_bytes();assert mirror.read_bytes()==b
old=json.loads((R/'milestones/166-small-loss-and-paper/data/completion.json').read_text());assert hashlib.sha256(b).hexdigest()==old['paper_sha256']
s=b.decode().replace('\r\n','\n');pre=s.split('\\begin{document}')[0]
anchor='\\begin{lemma}[Weighted window packing]'
insert=r'''\begin{lemma}[Undominated corners]\label{lem:undominated-corners}
Let every selected vertex have between one and two selected neighbours.
If $d(q)=0$, then $e(q)\ge4$. Equality forces at least eight selected
vertices of degree one. Consequently, for a nontrivial snake,
\[
d(q)=0\quad\Longrightarrow\quad e(q)\ge5.
\]
\end{lemma}
\begin{proof}
Translate $q$ to zero. The minimum-degree hypothesis makes zero
unselected, and $d(0)=0$ makes every weight-one vertex unselected.
An empty square through zero therefore corresponds exactly to an
unselected weight-two vertex, identified with its pair of directions.

At most one direction can occur in none of these missing pairs.
Indeed, suppose two directions $a,b$ are unused. The vertex with support
$\{a,b\}$ is selected. Its weight-one neighbours are unselected.
Every other neighbour has support $\{a,b,k\}$. If selected, that triple
vertex would have the three selected neighbours with supports
$\{a,b\},\{a,k\},\{b,k\}$, contradicting the maximum degree two.
The pair vertex would thus have no selected neighbour, also impossible.
The missing pairs cover at least eight directions. Each covers two,
so there are at least four of them.

If there are exactly four, their eight incidences cover eight different
directions. They form four disjoint pairs, leaving one unused direction
$c$. For each of the eight matched directions $a$, let $a'$ be its partner.
The vertex with support $\{c,a\}$ is selected. A triple neighbour
$\{c,a,k\}$ with $k\ne a'$ would again have three selected pair neighbours.
Its only possible selected neighbour is therefore $\{c,a,a'\}$, and
minimum degree forces this neighbour to occur. Each of the eight distinct
vertices $\{c,a\}$ has degree one. A nontrivial path has exactly two such
vertices, excluding equality and giving $e(q)\ge5$.
\end{proof}

\begin{corollary}\label{cor:small-loss-domination}
If a nontrivial snake satisfies $\sum_qr_{12}(q)\le59$, every vertex of
$\Q_9$ has a selected neighbour. In particular this holds in the target
case $\sum_qr_{12}(q)\le3$.
\end{corollary}
\begin{proof}
An undominated vertex would contribute $12e(q)\ge60$ to the nonnegative
remainder sum, contradicting its assumed upper bound.
\end{proof}

The coordinate argument above is a written geometric proof. The local
pair-and-triple implications and the final incidence and loss arithmetic
have passed Lean checks under explicit premises. Their complete
interpretation in $\Q_9$, including the matching and endpoint count,
remains to be assembled in Lean. The degree-only bound four is sharp:
select all weight-two vertices except four disjoint pairs, together with
all weight-three vertices containing one of those pairs. This gives
60 vertices, four three-vertex paths and six eight-cycles, with eight
endpoints and exactly four empty squares at zero. It is not a snake.
The printed 191-edge snake already has a selected neighbour at every
cube vertex, so the domination condition alone supplies no improved
length bound.

'''
assert s.count(anchor)==1;s=s.replace(anchor,insert+anchor)
a='A concrete next target is to\nexclude total loss at most three under the full path conditions.'
c='A concrete next target is to\nexclude total loss at most three under the full path conditions.\nCorollary~\\ref{cor:small-loss-domination} restricts this target to snakes\nwhose selected neighbourhoods cover the whole cube.'
assert s.count(a)==1;s=s.replace(a,c)
assert s.split('\\begin{document}')[0]==pre
out=s.replace('\n','\r\n').encode() if b'\r\n' in b else s.encode();p.write_bytes(out);mirror.write_bytes(out)
(H/'data/paper-edit.json').write_text(json.dumps(dict(before_sha256=hashlib.sha256(b).hexdigest(),after_sha256=hashlib.sha256(out).hexdigest(),preamble_unchanged=True,last_full_revision=166,latest_addition=167,next_full_revision=176,full_Q9_Lean_interpretation_pending=True),indent=2)+'\n',encoding='utf-8')
print('Added undominated-corner lemma and explicit verification scope to existing paper.')
