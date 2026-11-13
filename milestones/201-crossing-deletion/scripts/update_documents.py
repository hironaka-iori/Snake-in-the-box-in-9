from pathlib import Path
import hashlib,json,re

H=Path(__file__).resolve().parents[1]
R=H.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s): p.write_bytes(s.replace('\r\n','\n').encode('utf-8'))

section=r'''
\subsection{Crossings and deletions between two parent paths}
\label{sec:crossing-deletion201}
The following argument applies to every relative placement of the parent
paths, including placements without symmetry. It separates a general
dimensional construction restriction from the finite families above.

\begin{proposition}[Two-parent crossing identity]
\label{prop:crossing-deletion201}
Let $P,Q$ be induced paths of positive lengths $p,q$ in $Q_n$, placed
in opposite faces of $Q_{n+1}$, and put $N=p+q+2$.
Delete $D$ vertices from these layered copies and add $A$ vertices
outside their original union. Suppose that the entire resulting induced
graph is one nonempty path of length $L$, with $k$ edges across the
new coordinate. Let $b$ count deleted original endpoints, separately
in each parent, $e$ count original within-parent edges deleted at both
ends, and $H$ count final within-face edges incident to an added vertex,
each edge once. Then
\begin{equation}\label{eq:crossing-deletion201}
\boxed{k+b+e+H=1+D+A,\qquad L+k+b+e+H=N+2A.}
\end{equation}
In particular, if $p,q\le a(n)$, then
\begin{equation}\label{eq:crossing-bound201}
\boxed{L+k\le2a(n)+2+2A.}
\end{equation}
\end{proposition}
\begin{proof}
Initially the within-face edge count is $N-2$. The sum of the original
within-parent degrees of deleted vertices is $2D-b$. An edge whose two
ends are deleted occurs twice in this sum, so exactly $2D-b-e$ original
within-face edges disappear. The final vertex and edge counts satisfy
\[
L+1=N-D+A,\qquad L=N-2-2D+b+e+H+k.
\]
Subtracting gives the first identity; eliminating $D$ gives the second.
The bound follows from $N\le2a(n)+2$ and $b,e,H\ge0$.
\end{proof}
The same proof works in $G\square K_2$ for any simple graph $G$.
Positive-length parents ensure that each original endpoint has degree
one. A singleton parent would require degree deficit two in place of
one. The final path may be a singleton; the empty graph is excluded.
The hypothesis concerns every edge of the induced graph, including
any unwanted chord.

\begin{corollary}[Deletion and projected overlap]
\label{cor:overlap201}
If $A=0$, then $H=0$ and
\[
k=1+D-b-e,\qquad L=N-k-b-e,\qquad k\le D+1.
\]
For the original projected intersection $C=|V(P)\cap V(Q)|$,
\[
C\le D+k=1+2D-b-e,\qquad
D\ge\left\lceil\frac{C-1}{2}\right\rceil.
\]
If $C=D+k$, each deleted copy has a shared projection whose opposite
copy is retained.
\end{corollary}
\begin{proof}
The original cross-face edges form a matching of size $C$. Each edge
either survives or has a deleted endpoint; one deletion can destroy
only one such edge. This proves $C\le D+k$. More precisely, if $t$
counts original crossing edges deleted at both ends, and $z$ counts
deletions outside the original intersection, then $C+t+z=k+D$.
Equality forces $t=z=0$. The remaining claims follow from
\eqref{eq:crossing-deletion201}.
\end{proof}
The inequality $C\le D+k$ continues to hold with additions, since
surviving original crossings are a subset of all final crossings.
These counts are necessary restrictions and do not ensure connectivity.

\paragraph{Exactly one deletion.}
With no additions and one deleted original endpoint, $k=1$.
The retained part of that parent and the intact other parent join
exactly when their projected intersection is a single common endpoint.
The initial intersection has size one or two.

For an internal deletion, write $P=(p_0,\ldots,p_p)$ and delete
$x=p_i$, where $1\le i\le p-1$. The two surviving pieces
$P^-=(p_0,\ldots,p_{i-1})$ and $P^+=(p_{i+1},\ldots,p_p)$ are
nonempty, disjoint and nonadjacent. There are exactly two crossings.
Writing $Q=(q_0,\ldots,q_q)$, the retained graph is an induced path
if and only if there are
\[
u\in\{p_0,p_{i-1}\},\qquad v\in\{p_{i+1},p_p\}
\]
with
\begin{equation}\label{eq:one-deletion201}
\{q_0,q_q\}=\{u,v\},\qquad
\bigl(V(P)\setminus\{x\}\bigr)\cap V(Q)=\{u,v\}.
\end{equation}
For necessity, connectivity attaches each piece to $Q$ once.
The attachments must use endpoints, since an internal vertex already
has degree two. For sufficiency, traverse $P^-$, $Q$, $P^+$ in the
appropriate orientations. The intersection condition supplies exactly
the intended crossings, and original inducedness excludes all other
edges. This also covers singleton pieces.

Thus $C=2$ or $3$. If $C=3$, then $x\in V(Q)$. Choosing both
$u=p_{i-1}$ and $v=p_{i+1}$ makes $x$ adjacent to both endpoints
of $Q$. Its position on the induced path must then be both $1$ and
$q-1$, giving $q=2$. Hence for $q>2$ and $C=3$, at least one
attachment must be an original endpoint of $P$.

\paragraph{The distinction between the lower-dimensional constructions.}
For a 50-edge $Q_7$ snake obtained by deletions from two $Q_6$ parents,
$a(6)=26$ and \eqref{eq:crossing-bound201} give $k\le4$.
The saved 50-edge representative has a two-crossing split, with pieces
of lengths $18,24,6$, and a three-crossing split. These satisfy this
necessary restriction. Completion of their face forests to suitable
parent paths is a further requirement.

For a 98-edge $Q_8$ snake obtained by deletions from two $Q_7$ parents,
the same bound gives $k\le4$. At $k=4$, equality forces $p=q=50$,
$D=3$ and $b=e=0$: three isolated internal omissions.
The saved 98-edge representative has crossing counts
\[
(14,21,5,13,26,4,7,8)
\]
in coordinates $0,\ldots,7$. Its only four-crossing split, coordinate
5, has face sizes $47$ and $52$. A $Q_7$ parent contains at most 51
vertices. Every coordinate therefore violates either the crossing bound
or the parent size bound. This particular 98-edge snake cannot be
obtained solely by deleting vertices from two $Q_7$ parent paths in
any coordinate split. Cube isometries preserve this conclusion.
It is a restriction on the displayed witness, with no assertion about
all optimal $Q_8$ snakes. Its face forests require a more general
construction than this two-parent deletion model.

\paragraph{The 196-edge target.}
For $p,q\le98$, no additions and $L=196$, the vertex count and
\eqref{eq:crossing-bound201} imply $D\le1$ and $k\le2$.
The only parent sizes are $98,97$ with no deletion, or $98,98$ with
one deletion. In the first case the parents meet at a single common
endpoint. In the second case an endpoint deletion gives a one-crossing
join, while an internal deletion gives exactly
\eqref{eq:one-deletion201}: an intact 98-edge middle path and outside
pieces totalling 96 edges. In particular, $C\ge4$ excludes a
deletion-only 196-edge construction from two 98-edge parents.
When $C=3$, both newly exposed endpoints cannot serve as attachments.
A mixed choice of one original and one exposed endpoint requires $i$
odd, since the endpoints of a 98-edge cube path have the same colour.
The historical endpoint-aligned placement census does not automatically
cover attachments at newly exposed endpoints.

Allowing additions and requiring $k\ge4$ gives $A\ge1$.
If $A=1$, equality is forced:
\[
p=q=98,\quad D=2,\quad k=4,\quad b=e=H=0.
\]
Both omissions are internal and no original within-parent edge joins
them. The added vertex has no selected neighbour in its own face.
Since it has at most one neighbour across the new coordinate, it must
be a global endpoint. Removing it leaves a deletion-only 195-edge
snake with three crossings, and hence $C\le5$.

If $C=5$, the equality case of Corollary~\ref{cor:overlap201}
forces the opposite copy of each deleted projection to remain.
The added endpoint cannot attach across the coordinate at an endpoint
exposed by such a deletion: it would also be adjacent within its face
to that retained opposite copy, contradicting $H=0$.
Thus at $C=5$ it must attach to an original parent endpoint.
Consequently at least two additions are necessary if both final
endpoints must be retained original vertices. Without this endpoint
condition, the one-addition alternative remains unresolved.

\paragraph{Scope of the proof checks.}
Lean checks the Boolean-list edge and vertex accounting for arbitrary
parent lengths, the two-parent composition under the explicit final
vertex and edge count equations, and the numerical equality deductions.
It also checks the induced-path endpoint lemma, the common-neighbour
restriction, the overlap equality and the concrete coordinate obstruction
for the 98-edge witness. Two small induced paths verify sharpness of
the one-deletion overlap bound and the endpoint-addition possibility.
The identification of all counts with an arbitrary geometric
construction, the complete one-deletion classification and the composed
$C=5$ attachment conclusion have the written proofs above; their full
geometric assembly has not been checked in Lean. None of these results
gives a longer $Q_9$ snake or a new global numerical bound.

'''

frontier=r'''
\paragraph{Fundamental restrictions on dimensional constructions.}
Let two positive-length parent paths of lengths $p,q\le a(n)$ lie
in opposite faces. Delete $D$ original vertices and add $A$ vertices
outside the original copies. Assume the entire final induced graph is
a path of length $L$ with $k$ crossings between faces. Let $b$ count
deleted original endpoints, $e$ count original within-parent edges
deleted at both ends, and $H$ count final within-face edges touching
an added vertex, each edge once. Then
\[
\boxed{L+k+b+e+H=p+q+2+2A,\qquad L+k\le2a(n)+2+2A.}
\]
The proof is an edge count. Initially there are $p+q$ within-face
edges. Deleting vertices removes $2D-b-e$ of them. Adding the $H$
new within-face edges and $k$ crossings gives all final edges, while
the final vertex count is $p+q+2-D+A=L+1$.

Without additions, the same calculation gives $k=1+D-b-e$.
If $C$ is the original projected intersection, its cross-face edges
form a matching. Every destroyed crossing needs a deletion, so
$C\le D+k$ and $D\ge\lceil(C-1)/2\rceil$.
These restrictions apply to two specified parent paths; an arbitrary
higher-dimensional snake need not have such a representation.

The 50-edge $Q_7$ representative has a two-crossing split and is not
excluded by the resulting bound $k\le4$ for two $Q_6$ parents.
For the saved 98-edge $Q_8$ representative, every split except one
has at least five crossings, violating $98+k\le102$.
The remaining split has four crossings and face sizes 47 and 52.
A $Q_7$ parent has at most 51 vertices. Thus this witness cannot
be obtained by deletions alone from two $Q_7$ parents in any
coordinate split. The concrete coordinate obstruction passes Lean.
This conclusion explains a limitation of extrapolating the earlier
construction through two complete parent paths.

For 196 edges in $Q_9$, deletion alone from two parents of length
at most 98 permits at most one deletion and two crossings.
An internal deletion splits one 98-edge parent into two pieces.
The intact 98-edge parent must join these pieces through its two
endpoints, and those two attachment points must be the only retained
projected intersections. The initial intersection therefore has size
two or three. This is an exact criterion, with a written necessity
and sufficiency proof in the main paper.

If four or more crossings are required, at least one addition is
necessary. With exactly one addition, equality forces two 98-edge
parents, two isolated internal omissions, exactly four crossings and
$b=e=H=0$. The added vertex has no same-face neighbour and is
therefore a global endpoint. Removing it leaves a 195-edge,
three-crossing snake with $C\le5$. At $C=5$, every omitted shared
projection retains its opposite copy. That copy prevents attachment
at an endpoint exposed by a deletion, so the new endpoint must
attach at an original parent endpoint. If both final endpoints must
be original vertices, at least two additions are required instead.
Existence of the one-addition alternative remains unresolved.

Six new Lean modules check 24 theorem statements or dependency reports,
covering the list accounting, endpoint geometry, overlap equality and
concrete coordinate obstruction. The complete interpretation for arbitrary
geometric constructions and the one-deletion classification remain
written proofs. The next theoretical question is whether suitably
placed 98-edge parents satisfy the exact one-deletion criterion, or
produce the necessary 195-edge predecessor. No new witness or global
bound follows from the restrictions alone.

'''

records={}
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=EDITOR/name; mirror=R/'paper'/name
    assert p.read_bytes()==mirror.read_bytes(),name
    s=p.read_text(encoding='utf-8')
    before=sha(p)
    author=re.search(r'\\author\{[^\n]*\}',s).group()
    hyper=re.search(r'\\hypersetup\{.*?\n\}',s,re.S)
    if name=='snake9_research.tex':
        anchor=r'\section{Construction experiments and their scope}\label{app:experiments}'
        assert s.count(anchor)==1 and 'sec:crossing-deletion201' not in s
        s=s.replace(anchor,section+anchor)
        anchor='in Lean; the numerical placement censuses retain their separate scope.\n'
        assert s.count(anchor)==1
        s=s.replace(anchor,anchor+'A general two-parent identity gives $L+k\\le2a(n)+2+2A$, where\n$k$ counts crossings and $A$ counts added vertices. It excludes a\ndeletion-only two-parent representation of the displayed 98-edge snake\nand sharply restricts such constructions of a 196-edge snake.\n')
    else:
        s=s.replace('Research state after round 200','Research state after round 201')
        s=s.replace('through nine, with 194 as a provisional target and no new witness.','through nine, with general restrictions on two-parent constructions\nand no new witness.')
        anchor=r'\textbf{7. What is proved, and what remains.}'
        assert s.count(anchor)==1
        s=s.replace(anchor,frontier+anchor)
        s=s.replace('research records 175--200','research records 175--201')
    assert author in s
    if hyper: assert hyper.group() in s
    write(p,s);mirror.write_bytes(p.read_bytes())
    records[name]=dict(before_sha256=before,after_sha256=sha(p),editor=str(p),mirror=str(mirror),identical=True,author_preserved=True,hypersetup_preserved=True)

handoff='''# Current state after round 201

The user requested fundamental proofs and a pause at the end of this round. Finish publication, confirm the push, set the goal to paused, and stop. Resume only on a new user instruction. No new Q9 witness or global bound was obtained. Read milestones/201-crossing-deletion/MATHEMATICAL_NOTE.md and data/completion.json.

For two positive-length parent paths P,Q in opposite faces, N=p+q+2, delete D original vertices and add A outside the original copies. Assume the entire final induced graph is a nonempty path of length L, with k crossings. If b counts deleted original endpoints, e counts original within-parent edges deleted at both ends, and H counts final within-face edges touching additions once, then k+b+e+H=1+D+A and L+k+b+e+H=N+2A. Therefore L+k<=2a(n)+2+2A. These are necessary restrictions on this construction family, not a global bound. Initial projected overlap satisfies C<=D+k. In the deletion-only equality C=D+k, every deleted projection has its opposite copy retained.

Six Lean modules pass with 24 reports: CrossingDeletion201, LayerEndpoint201, TwoParents201, EndpointGeometry201, OverlapEquality201 and CutObstruction201. They check generic list counting, composition under the explicit final vertex/edge count equations, equality arithmetic, actual induced-path endpoint geometry, exact overlap and the concrete Q8 coordinate obstruction. The full geometric graph-to-count assembly, complete one-deletion iff and composed C=5 restriction have written proofs; do not present those full statements as Lean-assembled. Failed attempts and prior execution plans are archived. Two small induced-path examples are checked by kernel computation. No construction solver ran this round.

The saved98-edge Q8 witness cannot be obtained by deleting vertices from two Q7 parent paths in any coordinate split. All but coordinate5 have at least5 crossings, violating98+k<=102. Coordinate5 has4 crossings and face sizes47,52; each Q7 parent has at most51 vertices. The concrete all-coordinate alternative is kernel-checked from the99 actual vertices, which match the round188 seed. This statement covers cube images of this witness, not all optimal Q8 snakes. The saved50-edge Q7 representative has two- and three-crossing splits compatible with the necessary k<=4 bound; existence of containing Q6 parents is not established.

A deletion-only196-edge construction from two parents of length<=98 has D<=1,k<=2. It is either a98+97 one-crossing join, or two98-edge parents with one deletion. For an internal deletion, the intact parent is the98-edge middle path, joined to both remaining pieces at its endpoints; these two ports must be the only retained projected intersections. C<=3. If C=3, both ports cannot be the exposed neighbours of the deleted vertex. Mixed original/exposed ports require odd deletion index. The historical endpoint-aligned322560-placement census does not automatically cover this class.

For196 edges, k>=4 and A=1, equality forces p=q=98,k=4,D=2,b=e=H=0. The sole addition must be a global endpoint. Removing it leaves a195-edge,3-crossing predecessor with two isolated internal omissions and C<=5. If C=5, the added endpoint must attach to an original parent endpoint, because a retained opposite copy blocks attachment at a deletion-exposed endpoint. At least two additions follow only if both final endpoints must be retained original vertices. An earlier commentary asserted that two additions were always necessary; it was explicitly corrected before publication. No existence or impossibility result for the one-addition equality case was obtained.

On a new resume, prioritize these fundamental questions: characterize compatible placements of two98-edge parents for the exact one-deletion196 criterion, or for the195-edge3-crossing predecessor. Further symmetry reductions must preserve all original/exposed attachment choices. Complete the actual graph-to-count Lean assembly where it can support a useful conclusion. Do not treat scalar counts, degree bounds or Euler's edge count as sufficient for connectivity. The note includes a disconnected edge-plus-square counterexample.

The previous numerical route is secondary: round200 contains15 inverse-pair representatives for four-omission100-vertex paired-face repairs, of which cases4 and13 are excluded and13 remain unrun. Its complete native trimming maximum is92 separated vertices from two trimmed copies of one specified Q7 parent. Six-omission timeouts are unresolved. Do not rerun them unchanged or resume the catalogue merely because the goal restarts; the user's latest priority is fundamental proofs.

Contributor branch origin/research/unconditional-241 advanced from0cb8450707e481db49b6204587e45db9ae0df589 to816bbcf557c946227151bc4cee48357f1e7a4d65. Its05:49 UTC progress entry reports3005/3127 certificate modules built. This is the contributor's report, not a local independent rebuild. No merge or rebuild was performed. Archived235 independent rebuild remains pending;233/234 remain conditional. The final fetch and diff are archived in this round. Next whole-manuscript review remains210; round201 adds a focused construction section and updates the abstract/frontier.

Keep the existing editor sources D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, mirrored in E:/Snake-in-a-box/paper. Preserve all three authors and local hypersetup settings. Preserve the unrelated .gitignore and milestone50 critical-family.json edits. One heavy worker; at least1GiB free at Lean startup,768MiB reserve,256MiB private per Lean process,60-second limit, -j1. No background research is scheduled after pausing.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:write(R/'handoff'/name,handoff)
readme='''# Current result after round 201

General two-parent accounting gives L+k<=2a(n)+2+2A, linking final length, face crossings and added vertices. It excludes a deletion-only two-parent representation of the displayed98-edge Q8 witness and sharply restricts196-edge constructions. Six Lean modules pass with24 reports; full geometric interpretation and the exact one-deletion classification retain explicit written-proof scope.

No new Q9 witness or global bound was obtained. The user requested a pause after this round. Read [round201](milestones/201-crossing-deletion/README.md), [the proof](milestones/201-crossing-deletion/MATHEMATICAL_NOTE.md), [verification](milestones/201-crossing-deletion/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex). Resume only on new user instruction.

## Earlier checkpoints

'''
p=R/'README.md';assert p.read_text(encoding='utf-8').startswith('# Current result after round 200')
write(p,readme+p.read_text(encoding='utf-8'))
write(H/'data/document-edits.json',json.dumps(records,indent=2)+'\n')
print('UPDATED_EDITOR_AND_MIRRORS',json.dumps(records))
