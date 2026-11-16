from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):
    assert s.count(a)==1,a[:100]
    return s.replace(a,b,1)
main=(D/'snake9_research.tex').read_text(encoding='utf-8');short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=once(main,'Research state after round 231, 16 November 2026','Research state after round 232, 16 November 2026')
main=once(main,'parity class of the saved seed bank.','parity class of the saved seed bank. The complementary fixed-minority\ncase is also excluded. Thus a 192-edge construction must change both\nparity classes relative to each saved seed, under the stated native\nfinite evidence.')
main=once(main,'crossings and the opposite class free.','crossings and the opposite class free. Section~\\ref{sec:minority232}\ncompletes the complementary fixed-minority case.')
main=once(main,'That distinct construction case is the next target.','That distinct construction case is addressed next.')
section=r'''\subsection{The complementary fixed-minority construction}
\label{sec:minority232}
For a fixed minority class $U$, internal labels still have exactly two
neighbours in $U$, while endpoint labels have exactly one. A member of
$U$ is an eligible contracted endpoint if a singleton-neighbour label
exists there.

\begin{proposition}\label{prop:minority232}
For $|U|\ge2$, an induced path with minority class exactly $U$ exists if
and only if its two-neighbour contraction graph has a Hamiltonian path
whose two ends are eligible. Its edge length is $2|U|$.
\end{proposition}
\begin{proof}
Interleave the Hamiltonian order with its internal labels as in
Proposition~\ref{prop:colour231}, then attach singleton-neighbour labels
at its two ends. Those labels differ because their unique neighbours
differ. They differ from internal labels, whose selected-neighbour sets
have size two. Same-parity pairs are nonadjacent and the exact neighbour
sets permit only intended cross-parity adjacencies. The path has $|U|$
fixed vertices, $|U|-1$ internal labels and two endpoint labels.
Conversely, deleting the endpoints of an induced path with minority
class $U$ gives precisely such an interleaving, and each deleted endpoint
has one neighbour in $U$.
\end{proof}

Four further Lean results check endpoint/internal label distinction,
two-endpoint attachment to an actual induced path, the minority
constructor, and the singleton-neighbour property extracted from actual
path endpoints. Literal cube classes and graphs remain separate inputs.

Of the 145 saved labelled classes of size 96, two have fewer than two
eligible ends and 62 have an ineligible leaf. A Hamiltonian path must end
at every graph leaf. All other 81 cases are natively infeasible in a
circuit model with a dummy vertex adjacent only to eligible ends.
In 33 augmented graphs, deleting a set $S$ of one or two vertices leaves
more than $|S|$ components. A Hamiltonian cycle can leave at most $|S|$
path pieces after such a deletion. These are elementary explanations;
the other 48 cases retain their native circuit evidence.

Combining the two finite covers, any 192-edge snake must omit at least
one vertex of each parity from every saved seed. Otherwise an entire
96-vertex seed class would be its minority class or a subset of its
97-vertex majority class, both excluded. The conclusion transports to
cube-isometric seed copies by applying the inverse automorphism, which
preserves parity classes up to exchange. It depends on the native finite
exclusions and gives no global upper bound~\cite{research232}.

The next search may change the minority class by one vertex. Starting
with 95 retained vertices, inserting a new vertex changes only its nine
opposite-parity neighbours: selected-neighbour counts zero, one and two
become one, two and three. This gives a local update of endpoint and
internal labels. No complete search of that enlarged family is claimed.

'''
main=once(main,r'\section{A numerical conjecture and its limitations}',section+r'\section{A numerical conjecture and its limitations}')
marker='Full-source reviews at rounds 220 and 230 check the written argument,'
main=once(main,marker,r'''Section~\ref{sec:minority232} adds four checked endpoint and minority
construction results. Its 145-class exclusion and 33 separator
certificates retain their native extraction and verification scope.
'''+marker)
short=once(short,'Research state after round 231','Research state after round 232')
short=once(short,r'remains the next construction target~\cite{research231}.',r'is addressed below~\cite{research231}.')
section=r'''\section{Why both colour classes must change}
Now keep a saved 96-vertex class as the minority class. An internal
opposite-parity vertex still needs two neighbours there, while an
endpoint needs exactly one. The contracted Hamiltonian path must start
and end at vertices admitting those endpoint labels. Inserting the
internal labels and endpoints gives $96+95+2=193$ vertices and 192 edges,
with no additional adjacency.

All 145 classes were covered. Two lack two eligible ends, 62 have an
ineligible leaf, and the other 81 queries are infeasible. In 33 of those
cases a small separator splits the augmented cycle graph into too many
components. The other 48 retain native solver evidence. Lean checked
the endpoint attachment, minority construction and supporting neighbour
statements; the finite survey remains separate.

Together with the majority result, this means every 192-edge snake must
omit at least one vertex of each parity relative to every saved seed.
Keeping a whole 96-set would put it in one of the excluded cases. The
conclusion also holds for cube-isometric copies by transforming a
proposed candidate back to the saved coordinates. It retains the native
finite-evidence qualification and gives no new global bound~\cite{research232}.
The next route allows one vertex of the minority class to change, with
the other class still free. This enlarged family has not been exhausted.

'''
short=once(short,r'\section{Remaining questions}',section+r'\section{Remaining questions}')
short=once(short,'The parity-class comparison above supplies a broader exclusion while\nleaving the fixed-minority construction open. Wider blocks, changed\nblock lengths and changes to both colour classes remain possible.','The parity-class comparisons exclude keeping either entire class of a\nsaved seed. Changes to both classes, wider blocks and changed block\nlengths remain possible.')
short=once(short,'milestones through round 231','milestones through round 232')
bib=r'''\bibitem{research232}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Minority-class contraction and
the need to change both parity classes}. Research milestone 232,
16 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/232-minority-contraction}.

'''
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
    text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}');p=D/name;p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes());print('UPDATED',name)
p=H/'logs/minority-proof.md';p.write_text('Compilation update: all four reports passed the guarded Lean compiler. See data/MinorityContraction232-audit.json. Preparation-time statements below are historical.\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8',newline='\n')
