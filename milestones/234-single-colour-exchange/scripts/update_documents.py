from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):
 assert s.count(a)==1,a[:100]
 return s.replace(a,b,1)
main=(D/'snake9_research.tex').read_text(encoding='utf-8');short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=once(main,'Research state after round 233, 16 November 2026','Research state after round 234, 17 November 2026')
main=once(main,'near-doubling by deleting from the saved parents of lengths 26, 50 and 98.','near-doubling by deleting from the saved parents of lengths 26, 50 and 98.\nA complete one-replacement minority-class cover further shows that any\n192-edge snake shares at most 189 vertices with each saved 191-edge seed,\nunder the stated finite and native evidence.')
main=once(main,'The next search may change the minority class by one vertex. Starting','Section~\\ref{sec:exchange234} considers changing the minority class by\none vertex. Starting')
main=once(main,'No complete search of that enlarged family is claimed.','The complete cover of this enlarged family is given there.')
main=once(main,'The next constructive family replaces one vertex of a saved minority\nclass, with its opposite class and ordering free. It has not been\nsearched. This permits additions outside the old base path while\nretaining the exact contraction criterion.','The next subsection replaces one vertex of a saved minority class,\nwith its opposite class and ordering free. This permits additions\noutside the old base path while retaining the exact contraction criterion.')
section=r'''\subsection{Changing one member of a parity class}
\label{sec:exchange234}
For a selected class $U$, remove $d\in U$ and insert a same-parity
vertex $a\notin U$. Let $U'=(U\setminus\{d\})\cup\{a\}$. Each label $z$
has the exact updated neighbour set
\[
 N_{U'}(z)=(N_U(z)\setminus\{d\})\cup(\{a\}\cap N(z)).
\]
This follows directly by considering membership of each vertex. The
complete set is unchanged precisely when $z$ sees neither $d$ nor $a$.
If it sees both, its degree is unchanged but the neighbour identities
change. Previously unusable labels must also be considered: a label
of degree zero can become a singleton, while a label of degree three
can become an internal two-neighbour label. Four new checked statements
establish this exact update, its locality equivalence, and its singleton
and pair specializations. The finite degree-count consequences remain
written deductions.

The 145 saved labelled classes give
$145\cdot96\cdot160=2\,227\,200$ exchange descriptions. The static cover
has $1\,603\,284$ isolated-vertex exclusions, $616\,230$ excess-leaf
exclusions, 274 cases with fewer than two supported ends, 6019 with an
unsupported leaf, and 12 disconnected cases. The remaining 1381
descriptions represent 1325 distinct selected classes. An independent
reconstruction checked every complete resulting 96-set and every
decision, without using the producer's incremental graph updates.

Join a dummy vertex to all supported ends. A desired Hamiltonian path
is equivalent to a spanning cycle in this augmented graph. At a vertex
with two available edges, both must belong to a spanning cycle. Once
two incident edges are forced, all other incident edges are excluded.
Repeating these deductions gives four elementary contradictions: fewer
than two available edges, more than two forced edges, a forced cycle
on a proper subset, or multiple components after deletion of one vertex.
The last condition is impossible because deleting one vertex from a
spanning cycle leaves a connected path through all remaining vertices.

Exactly 1244 of the 1325 classes have these finite certificates, all
independently replayed from the literal cube graph. The other 81 retain
native circuit infeasibility evidence. The initial native batch excluded
771 classes before its time limit; the unfinished suffix was left open.
After the elementary certificates were applied, the final 22 uncovered
classes were excluded in a second native batch. Their union covers all
1325 classes. The elementary replay and native contradictions are
distinct from Lean certificate checking~\cite{research234}.

\begin{proposition}\label{prop:overlap234}
Under the stated finite covers, every 192-edge snake shares at most
189 vertices with each saved 191-edge seed and each cube-isometric
copy of such a seed. It omits at least three seed vertices and introduces
at least four vertices outside that seed.
\end{proposition}
\begin{proof}
The candidate's minority class has 96 vertices. An intersection of 96
with the corresponding seed class is excluded by the fixed-minority
cover; an intersection of 95 is exactly one replacement and is excluded
by the present cover. Thus this intersection is at most 94. The earlier
majority cover limits the intersection of its 97-vertex class with the
other seed class to 95. Their sum is at most 189. The seed and candidate
contain 192 and 193 vertices respectively, giving the stated omissions
and additions. For a cube-isometric seed copy, apply the inverse
automorphism; parity classes are preserved up to exchange.
\end{proof}

There is also an exact restricted maximum. If one complete parity class
has size 96 and differs from a saved class by at most one replacement,
alternation gives edge length at most 192. The top case would make that
class the minority class and is excluded. The maximum over this family is 191,
attained by an original seed in the zero-replacement case. This gives
no global upper bound.

The next construction allows two replacements in a saved minority
class. A joint optional-vertex circuit model can select the class and
ordering together, with exact selected-neighbour degrees excluding
chords. This avoids enumerating billions of descriptions individually.
That model is proposed and has not yet been run.

'''
main=once(main,r'\section{A numerical conjecture and its limitations}',section+r'\section{A numerical conjecture and its limitations}')
marker='Full-source reviews at rounds 220 and 230 check the written argument,'
main=once(main,marker,r'''Section~\ref{sec:exchange234} adds four checked exact-neighbour update
statements. Its complete static reconstruction, 1244 elementary replayed
certificates and 81 remaining native contradictions have separate scopes;
the overlap deduction is written from those finite premises.
'''+marker)
short=once(short,'Research state after round 233','Research state after round 234')
short=once(short,'A possible next route replaces one vertex of the minority class, with\nthe other class still free. This family has not been searched. The\nfollowing round first examines a smaller family built from old paths.','The one-replacement route is addressed below. The intervening round\nfirst examined a smaller family built from old paths.')
short=once(short,'The useful next family allows additions as well as deletions in a saved\nparity class, while leaving the opposite class and ordering free.\nResearch pauses after round 233.','This motivated allowing additions as well as deletions in a saved parity\nclass, while leaving the opposite class and ordering free. Research\nresumed after the round-233 pause.')
section=r'''\section{One replacement is still insufficient}
Replace one vertex of a saved 96-vertex minority class, leaving its
opposite class, endpoints and ordering free. The exact neighbour update
removes the old vertex and adds the new one wherever adjacent. A label
that sees both has the same degree but different neighbours; those
identities must be updated. Four general Lean statements check the
update and its relevant special cases.

All $2\,227\,200$ descriptions were examined and independently
reconstructed. Elementary isolated-vertex, leaf, endpoint and connectivity
conditions leave 1381 descriptions, representing 1325 distinct classes.
Of these, 1244 have independently replayed elementary contradictions.
For example, a vertex with only two available edges forces both into
the proposed spanning cycle; successive forced choices may close a
smaller cycle and prevent a single cycle through all vertices. The
remaining 81 classes retain native infeasibility evidence. Every case
is covered, with no 192-edge construction~\cite{research234}.

This sharpens the distance from every saved seed. A candidate's
96-vertex minority class can share at most 94 vertices with the
corresponding seed class: sharing 95 would be one replacement, and
sharing 96 would be the already excluded unchanged class. Its
97-vertex majority class can share at most 95 by the earlier cover.
Thus the candidate shares at most $94+95=189$ vertices with the seed.
Since the seed has 192 vertices and the candidate has 193, at least
three old vertices must be omitted and four new vertices introduced.
The argument also applies to cube-isometric seed copies, with the same
finite-evidence qualification. These changes are necessary and need
not be sufficient.

The next proposed experiment allows two replacements in a minority
class and chooses all other vertices and their ordering together.
It has not been run. The global interval is unchanged, and the goal
remains active.

'''
short=once(short,r'\section{Remaining questions}',section+r'\section{Remaining questions}')
short=once(short,'milestones through round 233','milestones through round 234')
bib=r'''\bibitem{research234}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Replacing one member of a parity class}.
Research milestone 234, 17 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/234-single-colour-exchange}.

'''
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
 text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}');p=D/name
 p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes());print('UPDATED',name)
p=H/'logs/exchange-proof.md';p.write_text('Compilation update: all four statements passed the guarded Lean compiler. See data/ColourExchange234-audit.json. Preparation-time status below is historical.\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8',newline='\n')
