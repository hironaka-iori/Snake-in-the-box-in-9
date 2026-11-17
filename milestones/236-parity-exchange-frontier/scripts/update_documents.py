"""Publish the mathematical argument in the existing editor sources."""
from pathlib import Path
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
D = Path('D:/Codex/2026-10-13/new-chat/outputs')


def once(s, a, b):
    assert s.count(a) == 1, a[:100]
    return s.replace(a, b, 1)


three = json.loads((H/'data/three-audit.json').read_bytes())
four = json.loads((H/'data/four-audit.json').read_bytes())
assert three['all_145_native_excluded'] and three['exchanges'] == 3
assert four['exchanges'] == 4
for module in ['ExchangeBalance236', 'AdjacencyInverse236']:
    assert json.loads((H/'data'/(module+'-audit.json')).read_bytes())['status'] == 'PASS'
four_rows = four['batches'][0]['rows']
four_text = '; '.join(f"class {row['base']}: \\texttt{{{row['status']}}}" for row in four_rows)
main = (D/'snake9_research.tex').read_text(encoding='utf-8')
short = (D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main = once(main, 'Research state after round 235, 17 November 2026', 'Research state after round 236, 18 November 2026')
main = once(main, 'Complete covers through two replacements of a minority class further\nshow that any 192-edge snake shares at most 188 vertices with each saved', 'Complete covers through three replacements of a minority class further\nshow that any 192-edge snake shares at most 187 vertices with each saved')
main = once(main, 'At least three minority replacements\nare required for the next construction attempt. Their feasibility has\nnot been investigated in this round.', 'The following subsection investigates three replacements and derives\nconsistency conditions for larger changes.')
section = r'''\subsection{Three replacements and consistency of larger changes}
\label{sec:exchange236}
The same degree formulation was next applied with exactly 93 retained
vertices from each saved 96-set. This represents three removals and three
insertions in the candidate's minority class. All 145 initial models
were natively infeasible, without a cycle cut. Independent reconstruction
checked all variables, constraints, selection guards and exchange counts.
The models implicitly cover
\[
145\binom{96}{3}\binom{160}{3}=13\,879\,134\,592\,000
\]
labelled exchange descriptions before duplicates. These native exclusions
have no Lean contradiction replay~\cite{research236}.

Together with the earlier covers, the minority intersection is at most
92, and the other intersection remains at most 95. Hence every 192-edge
snake shares at most 187 vertices with each saved seed or cube-isometric
copy, under the stated finite evidence. At least five old vertices must
be omitted and six new ones introduced. The same alternation argument
as before gives exact maximum 191 in the restricted family with one
complete 96-vertex parity class within three replacements of a saved
class; an original seed attains it. This is no global bound.

Four further searches with exactly four replacements gave the following
outcomes: FOUR_RESULTS. Each query had a 40-second limit. An unresolved
outcome supplies no exclusion, and these four classes are not a complete
cover of the saved collection.

\begin{lemma}[Balance at retained vertices]\label{lem:balance236}
Let $P,Q$ be the vertex sets of induced paths of positive length in the
same graph. Write $A=Q\setminus P$ and $D=P\setminus Q$. If $v\in P\cap Q$
and $e_P(v),e_Q(v)$ are its endpoint indicators, then
\[
 |N(v)\cap A|+e_Q(v)=|N(v)\cap D|+e_P(v).
\]
\end{lemma}
\begin{proof}
The retained neighbours contribute equally to the old and new degrees.
After cancelling them, the difference of the two degrees is the number
of added neighbours minus removed neighbours. The degrees are
$2-e_P(v)$ and $2-e_Q(v)$, which gives the identity.
\end{proof}
In particular, every retained internal minority vertex of a 191-edge
seed must have equally many added and removed majority neighbours in a
192-edge candidate. If a proposal violates this equality at an old
internal minority vertex, that vertex must be deleted. With $r$ minority
replacements there can be at most $r$ such vertices. A retained old
minority endpoint instead requires one extra added neighbour.

An added majority vertex incident to a retained internal minority vertex
must therefore have a deleted majority vertex at Hamming distance two.
The incidence hypothesis is essential: the induced path $(0,1,3,7)$ in
$\Q_3$ extends to $(0,1,3,7,6)$ without a deletion, because the new vertex
touches an old endpoint. The count conditions can guide compatible
changes; they are already consequences of the full degree model.

\begin{proposition}[Reconstruction from neighbour counts]
\label{prop:inverse236}
For any integer-valued function $z$ on $\Q_9$, put
$b(v)=\sum_{u\sim v}z(u)$ and set
\[
(c_0,c_1,\ldots,c_9)=(0,35,0,-10,0,8,0,-16,0,128).
\]
For every vertex $a$,
\[
 315z(a)=\sum_{v\in\Q_9}c_{\operatorname{dist}(a,v)}b(v).
\]
Consequently, the complete neighbour counts of a vertex set determine
that set uniquely.
\end{proposition}
\begin{proof}
Substitute the definition of $b$ and collect the coefficient of $z(u)$.
If $k=\operatorname{dist}(a,u)$, exactly $k$ neighbours of $u$ decrease
the distance and $9-k$ increase it. Odd $k$ gives zero. The even cases give
\[
\begin{aligned}
9(35)&=315, & 2(35)+7(-10)&=0, & 4(-10)+5(8)&=0,\\
6(8)+3(-16)&=0, & 8(-16)+128&=0.
\end{aligned}
\]
Only the coefficient for $u=a$ survives. Apply the formula to the
difference of two vertex-set indicators to obtain uniqueness.
\end{proof}

For changes on the majority side alone, $z$ takes values $-1,0,1$ and
the formula uses all 256 minority-side observations. Each weighted sum
must be $-315$, zero or $315$, with the selection sign fixed by the old
set. Counts at retained minority vertices follow
Lemma~\ref{lem:balance236}; the other counts remain unknown and cannot
be set to zero. Since the majority side gains one vertex, double counting
gives $\sum b(v)=9$ over the minority side. Its unretained vertices must
contribute eight if the old minority endpoint is retained, and nine
otherwise. These are consistency conditions, without a claim of
sufficiency or an improved solver runtime.

Four retained-count statements and two inverse-support statements passed
Lean. The latter establish the integer recurrences and a finite-sum
reconstruction theorem under an explicit matrix coefficient hypothesis.
The cube distance-count argument above supplies the written geometric
bridge. A separate exact integer calculation verifies all 262144 entries
of the full labelled-cube matrix identity. No complete cube instantiation
or native infeasibility replay is attributed to the new Lean checks.

'''.replace('FOUR_RESULTS', four_text)
main = once(main, r'\section{A numerical conjecture and its limitations}', section+r'\section{A numerical conjecture and its limitations}')
main = once(main, 'Full-source reviews at rounds 220 and 230 check the written argument,', r'''Section~\ref{sec:exchange236} adds six checked supporting statements,
an exact full-cube inverse calculation and an audited native cover of
all three-replacement families. The stated geometric bridges and native
contradictions retain their separate scope.
Full-source reviews at rounds 220 and 230 check the written argument,''')
short = once(short, 'Research state after round 235', 'Research state after round 236')
short = once(short, 'The next unsearched family permits three replacements in the minority\nclass. The degree formulation and cycle-separation code are saved for\nthat attempt. Research pauses after round 235 as requested.', 'The following round applies the saved degree formulation to three\nreplacements and investigates the conditions on larger changes.')
short_section = r'''\section{Three replacements and the next construction}
All 145 saved three-replacement families also fail the necessary degree
conditions. The exported models and the complete coverage were checked
independently. Their infeasibility remains native solver evidence.
Combining the covers through three replacements bounds the minority
intersection by 92. The majority intersection remains at most 95, so
the total overlap with any saved seed or its cube-isometric copy is at
most $92+95=187$. Thus a 192-edge candidate must omit at least five old
vertices and introduce at least six new ones.

The first four searches with exactly four replacements gave:
FOUR_RESULTS. These are only four saved classes; an unresolved result
does not establish impossibility.

There is a useful rule for choosing the changes. At an old internal
vertex that stays internal, every added neighbour must be balanced by
a removed neighbour. An old endpoint that becomes internal needs one
extra neighbour. This follows by subtracting its old and new degree
equations. After proposing majority-side changes, every old internal minority
vertex with unbalanced neighbour counts must be deleted, since all
retained minority vertices are internal in the candidate. This can identify required deletions before a complete search.

Nine-dimensional neighbour counts also have an exact inverse. If $b(v)$
is the change in the number of selected neighbours, the weighted sum of
all these changes around a vertex, with weights $35,-10,8,-16,128$ at
distances $1,3,5,7,9$, equals 315 times that vertex's selection change.
The proof counts how each cube step increases or decreases distance;
all coefficients cancel except the coefficient at the vertex itself.
Therefore complete neighbour counts determine the selected set uniquely.
Counts outside the retained snake are essential unknowns in this formula.

Six supporting statements passed Lean, while the full cube matrix was
checked separately by exact integer arithmetic. The geometric connection
and native exclusions have the stated separate scopes~\cite{research236}.
No longer snake or new global bound was obtained. The open construction
problem now starts with at least four minority replacements. Research
pauses after round 236; unresolved searches and the balance-guided route
are saved for resumption.

'''.replace('FOUR_RESULTS', four_text)
short = once(short, r'\section{Remaining questions}', short_section+r'\section{Remaining questions}')
short = once(short, 'milestones through round 235', 'milestones through round 236')
bib = r'''\bibitem{research236}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Larger parity exchanges and
neighbour-count reconstruction}. Research milestone 236, 18 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/236-parity-exchange-frontier}.

'''
for name, text in [('snake9_research.tex', main), ('snake9_frontier_explanation.tex', short)]:
    text = once(text, r'\end{thebibliography}', bib+r'\end{thebibliography}')
    (D/name).write_text(text, encoding='utf-8', newline='\n')
    (R/'paper'/name).write_bytes((D/name).read_bytes())
    print('UPDATED', name)
