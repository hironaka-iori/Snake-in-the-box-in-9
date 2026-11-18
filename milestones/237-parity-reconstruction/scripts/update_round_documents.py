"""Integrate the completed round-237 mathematics without replacing editor files."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):
    assert s.count(a)==1,a[:120]
    return s.replace(a,b,1)
assert json.loads((H/'majority/kernel-cuts.json').read_bytes())['status']=='PASS'
assert json.loads((H/'data/inverse-replay.json').read_bytes())['status']=='PASS'
assert json.loads((H/'data/spectral-replay.json').read_bytes())['status']=='PASS'
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
section=(H/'data/provisional-section.tex').read_text(encoding='utf-8')
section=section[section.index(r'\subsection{'):]
section=once(section,'A working hypothesis is that $a(9)=191$. A longer snake would have a\n192-edge prefix. To look for such a prefix, let $B$ be either 96-vertex\nparity class of a saved 191-edge path.','A longer snake would have a 192-edge prefix. The construction hypothesis\nexamined here is that a small change in the larger parity class might\npermit such a prefix. Let $B$ be either 96-vertex parity class of a saved\n191-edge path.')
section=once(section,'This\nquestion tests one consequence of the working hypothesis. The numerical\nconjecture in Section~\\ref{sec:hypothesis} makes a different prediction.','This\nquestion concerns the specified construction family and makes no global\noptimality claim.')
section=once(section,'Section~\\ref{sec:majority237} uses the following equivalence. A snake','The following equivalence guides the search. A snake')
section=once(section,'all 623 displayed-by-data inequalities have individual kernel checks.\nAn independent necessary-degree search excludes the same 145 families\nbefore imposing connectivity~\\cite{research237}. The correspondence from\nthe complete enumeration to the saved bank is computational evidence.','all 623 literal inequalities have individual kernel checks, rebuilt in\nsmall sequential modules. The correspondence between the numerical row\ncounts and the path-index cut theorem is given by the mathematical\nargument above; its complete proof-assistant assembly remains open.\nA separate audited necessary-degree model reports infeasibility for all\n145 families before imposing connectivity~\\cite{research237}. The\ncomplete enumeration and its correspondence to the saved bank remain\ncomputational evidence, separate from the numerical kernel checks.')
section += r'''
The original single-file cube check exceeded the retained memory limit.
Splitting its 512-case coefficient calculation into exhaustive prefix
cases allowed the same actual-cube theorem to be recompiled. The
accepted reconstruction and two-erasure statements have only standard
axiom dependencies. No symmetry assumption on the selected set is used.

'''
main=once(main,'Research state after round 236, 18 November 2026','Research state after round 237, 18 November 2026')
main=once(main,'Complete covers through three replacements of a minority class further\nshow that any 192-edge snake shares at most 187 vertices with each saved','Complete covers through three replacements of a minority class and a\nmajority-exchange cover show that any 192-edge snake shares at most 186\nvertices with each saved')
main=once(main,r'\section{A numerical conjecture and its limitations}',section+r'\section{A numerical conjecture and its limitations}')
main=once(main,'Full-source reviews at rounds 220 and 230 check the written argument,',r'''Sections~\ref{sec:majority237} and~\ref{sec:erasure237} add checked path
criteria, 623 checked numerical cuts, and actual-cube reconstruction with
two missing observations. Enumeration coverage and the complete
numerical-cut-to-path assembly retain their stated separate scopes.
Full-source reviews at rounds 220 and 230 check the written argument,''')
short=once(short,'Research state after round 236','Research state after round 237')
short=once(short,'Research\npauses after round 236; unresolved searches and the balance-guided route\nare saved for resumption.','The following round examines a complementary change on the majority\nside; unresolved four-replacement searches remain saved.')
newshort=r'''\section{Changing the majority class and recovering missing counts}
The complementary construction removes one vertex from a saved
96-vertex parity set and inserts two others of the same parity. These
97 vertices would be the majority class of a 192-edge snake. The other
96 vertices and the entire ordering remain free.

Join two majority vertices when some opposite-parity vertex has exactly
those two selected neighbours. A snake gives a path visiting every
majority vertex once in this simple graph. Conversely, such an ordering
can be interleaved with its witnessing vertices to give the snake.

This gives two useful necessary conditions. If $r$ majority vertices are
still missing from a partial proposal, its isolated vertices and leaves
satisfy $2I+L\le2r+2$. Removing $r$ positions from a spanning path leaves
at most $r+1$ runs, each contributing two missing incidences; additional
graph edges can only reduce the deficit. For a complete proposal and
arbitrary subsets $S,T$, counting the two directions along the path gives
\[
2|S|\le2|T|+2+e(S,U\setminus T).
\]
Here $e$ counts ordered edges from $S$ to vertices outside $T$. Only two
directions can end at path endpoints; vertices of $T$ receive at most two.

Two independent enumerations agree on all surviving proposals among
177,062,400 descriptions. There are 679 survivors representing 623
distinct sets. Each violates the displayed cut inequality for saved
explicit subsets. All 623 numerical inequalities passed kernel checking.
The full connection from numerical counts to the path theorem remains
a written argument, with its proof-assistant assembly incomplete. A
separate audited degree model also reports all 145 starting families
infeasible. Those native exclusions have no Lean contradiction replay.

Under these finite covers and the earlier ones, the majority overlap
with a saved seed is at most 94. Combined with the minority overlap
bound 92, the total is at most $94+92=186$.
A 192-edge candidate must therefore omit at least six old vertices and
introduce at least seven new ones, relative to every saved seed or its
cube-isometric copy. This remains a restriction on proximity to the
saved collection.

The cube reconstruction theorem has also been strengthened: neighbour
counts at any 510 of the 512 vertices determine a binary selection
uniquely. To see why two missing counts cannot conceal a change, apply
the inverse formula at their antipodes. Two integer equations result,
with diagonal coefficient 128 and a short list of possible off-diagonal
coefficients. The selection difference is $-1$, zero or one. The only
integer solution consistent with these equations has both missing
count changes zero. The inverse then makes the entire selection change
zero. This actual-cube statement passed Lean after the large finite
calculation was divided into smaller modules~\cite{research237}.

No longer snake was obtained. The current interval is $191\le a(9)\le231$
using the separately cited contributor theorem. Research continues
through rounds 238 and 239 as requested.

'''
short=once(short,r'\section{Remaining questions}',newshort+r'\section{Remaining questions}')
short=once(short,'milestones through round 236','milestones through round 237')
bib=r'''\bibitem{research237}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Majority exchanges and reconstruction
with missing neighbour counts}. Research milestone 237, 18 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/237-parity-reconstruction}.

'''
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
    text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}')
    (D/name).write_text(text,encoding='utf-8',newline='\n')
    (R/'paper'/name).write_bytes((D/name).read_bytes())
    print('UPDATED',name)
