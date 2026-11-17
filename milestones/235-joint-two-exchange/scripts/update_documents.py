from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):
 assert s.count(a)==1,a[:100]
 return s.replace(a,b,1)
main=(D/'snake9_research.tex').read_text(encoding='utf-8');short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=once(main,'Research state after round 234, 17 November 2026','Research state after round 235, 17 November 2026')
main=once(main,'A complete one-replacement minority-class cover further shows that any\n192-edge snake shares at most 189 vertices with each saved 191-edge seed,\nunder the stated finite and native evidence.','Complete covers through two replacements of a minority class further\nshow that any 192-edge snake shares at most 188 vertices with each saved\n191-edge seed, under the stated finite and native evidence.')
main=once(main,'That model is proposed and has not yet been run.','The next subsection implements this approach and a smaller necessary\ndegree formulation.')
section=r'''\subsection{Joint construction and the two-replacement obstruction}
\label{sec:joint235}
Choose the minority class and all other path vertices together. For a
saved 96-set $U$, select 96 minority and 97 majority vertices, with
exactly 94 selected from $U$. This specifies two removals and two outside
insertions. For each actual cube edge $vw$, let $x_v,x_w$ be its Boolean
selection indicators and $f,b$ its directed arc indicators. The constraints
\[
 f+b\le x_v,\qquad f+b\le x_w,\qquad
 f+b\ge x_v+x_w-1
\]
give $f+b=x_vx_w$. Thus every selected cube adjacency is used. Unselected
vertices take self-loops in an optional-vertex circuit; selected vertices
cannot. A mandatory dummy is joined only to selected majority vertices.
Removing it from the single circuit gives the required induced path.
Conversely, every target path gives such a circuit orientation. No old
ordering, opposite class, endpoint or crossing pattern is fixed.

The four initial queries, for saved classes 139, 7, 6 and 0, each returned
\texttt{UNKNOWN} after 60 seconds. Their complete 5632-variable models
were independently audited. These queries alone establish no exclusion.
Four new checked statements establish the Boolean edge identity,
its one-direction consequence, injectivity from exact successor arcs,
and an induced-path constructor. The extraction of the selected order
from the native circuit remains a separate bridge.

A smaller formulation uses selection indicators $x_v$ and endpoint
indicators $e_v$ on the majority class, with $e_v=0$ on the minority class. Require
$\sum e_v=2$ and $e_v\le x_v$, and impose
\[
 x_v=1\quad\Longrightarrow\quad
 \sum_{w\sim v}x_w=2-e_v.
\]
There is no degree restriction at an unselected vertex. Every target
snake satisfies these conditions. A feasible selected graph consists
of exactly one path joining the two endpoints and zero or more cycles:
all its degrees are one or two, and exactly two vertices have degree one.

An extracted cycle $C$ gives the valid inequality
$\sum_{v\in C}x_v\le |C|-1$, since an induced path cannot contain a cycle
as a subgraph. Earlier checked cycle-occupancy and selected-degree
statements support this method; their accepted source, object, log and
dependency hashes were rechecked. Literal graph extraction remains a
separate finite obligation. No cycle cut was needed in the present cover.

All 145 saved classes are natively infeasible in the initial degree
model with exactly two replacements. Each model has 768 Boolean
variables and 772 constraints, including 512 positively guarded degree
equations. Every variable, constraint, guard and evidence pin was
independently checked. The four initial degree queries took about
0.25--0.45 seconds each; the second batch covered the other 141 classes.
There are no unresolved cases in this cover. It represents
\[
145\binom{96}{2}\binom{160}{2}=8\,410\,464\,000
\]
exchange descriptions before duplicates. The contradiction already
occurs in the degree relaxation, before connectivity or ordering is
required. These are native finite exclusions, without a Lean replay
of the contradictions~\cite{research235}.

\begin{proposition}\label{prop:overlap235}
Under the stated finite covers, every 192-edge snake shares at most
188 vertices with each saved 191-edge seed or cube-isometric copy.
At least four seed vertices are omitted and five new vertices introduced.
\end{proposition}
\begin{proof}
Intersections of 96, 95 and 94 vertices between the candidate's minority
class and the corresponding seed class are excluded by the zero-, one-
and two-replacement covers. Hence this intersection is at most 93.
The earlier majority cover bounds the other intersection by 95. Their
sum is at most 188. The seed has 192 vertices and the candidate has 193,
giving the claimed omissions and additions. An inverse cube automorphism
transports the conclusion to isometric seed copies.
\end{proof}

If one complete parity class has size 96 and differs from a saved class
by at most two replacements, alternation bounds the edge length by 192.
That top case is excluded. The maximum over this restricted family is
therefore 191, attained by an original seed in its zero-replacement part.
This gives no global upper bound. At least three minority replacements
are required for the next construction attempt. Their feasibility has
not been investigated in this round.

'''
main=once(main,r'\section{A numerical conjecture and its limitations}',section+r'\section{A numerical conjecture and its limitations}')
marker='Full-source reviews at rounds 220 and 230 check the written argument,'
main=once(main,marker,r'''Section~\ref{sec:joint235} adds four checked circuit-to-path supporting
statements and an independently audited native degree-model cover of all
145 exact-two-replacement families. The native contradictions and full
solver-to-cube assembly remain outside that checked scope.
'''+marker)
short=once(short,'Research state after round 234','Research state after round 235')
short=once(short,'It has not been run. The global interval is unchanged, and the goal\nremains active.','The following round implements this approach. The global interval\nremains unchanged.')
section=r'''\section{Two replacements also fail the degree conditions}
The next model chooses 96 minority and 97 majority vertices together,
retaining exactly 94 vertices of a saved minority class. Four direct
circuit queries remained unresolved after a minute each.

A smaller model asks only for the necessary neighbour counts. Each
selected vertex must have two selected cube neighbours, except the two
majority endpoints, which have one. Unselected vertices are unrestricted.
Any actual snake satisfies these conditions. A feasible disconnected
selection would consist of one path and some cycles; verified cycle
inequalities could then remove those cycles.

All 145 saved classes were infeasible with two replacements even in
this smaller model, before any cycle inequality was needed. The models
jointly cover $8\,410\,464\,000$ replacement descriptions. Independent
inspection verified every model and its positive selection guards.
The infeasibility conclusions remain native solver evidence. Four new
Lean statements support the separate circuit-to-path argument; the
finite contradictions are not Lean certificate replays~\cite{research235}.

The important consequence is that the candidate's minority class can
now share at most 93 vertices with the corresponding saved class.
Its majority class can share at most 95 by the earlier result, so the
total overlap is at most $93+95=188$. A saved seed has 192 vertices and
a proposed 192-edge snake has 193. At least four old vertices must
therefore be omitted and five new ones introduced. This applies to
each saved seed and its cube-isometric copies under the same finite
evidence, and does not establish a global upper bound.

The next unsearched family permits three replacements in the minority
class. The degree formulation and cycle-separation code are saved for
that attempt. Research pauses after round 235 as requested.

'''
short=once(short,r'\section{Remaining questions}',section+r'\section{Remaining questions}')
short=once(short,'milestones through round 234','milestones through round 235')
bib=r'''\bibitem{research235}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Joint construction and the
two-replacement obstruction}. Research milestone 235, 17 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/235-joint-two-exchange}.

'''
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
 text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}');p=D/name;p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes());print('UPDATED',name)
p=H/'logs/circuit-proof.md';p.write_text('Compilation update: all four reports passed the guarded Lean compiler. See data/CircuitPath235-audit.json. Preparation-time status below is historical.\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8',newline='\n')
