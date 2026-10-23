"""Reorganize the existing manuscript from its committed research-round baseline."""
from pathlib import Path
import re, subprocess, json, hashlib

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
BASE='ffdf1b94403396a1b8ddaffdae419bb897ba5cf8'
old=subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode('utf-8').replace('\r\n','\n')
def between(a,b):
    return old[old.index(a):old.index(b)].strip()+'\n\n'
def block(label):
    pos=old.index('\\label{'+label+'}')
    start=old.rfind('\\begin{',0,pos)
    end=old.index('\\end{proof}',pos)+len('\\end{proof}')
    return old[start:end]+'\n\n'
def sec(name,nextname):
    return between('\\section{'+name+'}', '\\section{'+nextname+'}')
def sub(name,nextname):
    return between('\\subsection{'+name+'}', '\\subsection{'+nextname+'}')
def demote(s):
    return s.replace('\\subsection*{','\\subsubsection*{').replace('\\section{','\\subsection{')

preamble=old[:old.index('\\begin{abstract}')]
abstract=r'''\begin{abstract}
The maximum number of edges in an induced path of the nine-dimensional binary hypercube is denoted by $a(9)$. The results assembled here give $191\le a(9)\le238$. The lower bound is a published construction, reproduced as an explicit transition sequence. The upper bound follows from the exact identity $T+2s_0+35v=9214$, where $v$ is the number of selected vertices, $T$ is the total number of singleton squares, and $s_0$ is the number of empty squares. A finite family of 175 forbidden windows and an integer potential imply $2T\ge7(v-1)-36$, which yields the bound 238. The proof separates the geometric interpretation of each window, the checked finite refutations, and the summation argument. We then retain the empty-square term through integer shares, prove sharp two-position singleton inequalities, and establish a three-square share bonus and further overlap exclusions. These refinements have not yet produced a stronger uniform bound. Explicit counterexamples distinguish endpoint maximality and local feasibility from global optimality. The value 196 remains a numerical conjecture. The 238 theorem has a successful Lean dependency audit against an incrementally built Linux library; an independent rebuild of that complete theorem remains pending.
\end{abstract}
\clearpage
\setcounter{tocdepth}{1}
\tableofcontents
\clearpage

\section{Problem, notation, and principal result}\label{sec:problem}
'''
intro=between('\\begin{definition}', '\\begin{theorem}[Main result]')
intro=intro.replace('Its examples cannot be extended at their endpoints; that observation alone gives no maximum-length theorem.', 'The recorded examples are blocked at their endpoints. Section~\\ref{sec:optimality} explains why this does not establish optimality.')
main=r'''\begin{theorem}[Main result]\label{thm:main}
The maximum edge length of an induced path in $\Q_9$ satisfies
\[
\boxed{191\le a(9)\le238.}
\]
\end{theorem}
Theorem~\ref{thm:lower} proves the lower bound from a displayed sequence. The upper bound is deduced in Section~\ref{sec:upper-proof}. Its logical dependencies are as follows. Every selected vertex has at least one singleton square, and every endpoint has at least four. The exact square census converts a lower bound on the sum of these counts into an upper bound on length. A finite family of local exclusions supplies a potential inequality, whose sum gives the required lower bound. The computer-assisted steps are identified explicitly; the numerical search outcomes in the appendices are separate from these proof premises.

For a snake $P=(x_0,\ldots,x_m)$, write $S=V(P)$ and $v=|S|=m+1$. Thus $m$ always counts edges and $v$ counts vertices. A coordinate square is a two-dimensional face of the cube. Let $s_k$ count the distinct coordinate squares containing exactly $k$ vertices of $S$. For $x\in S$, let $\alpha_S(x)$ count squares meeting $S$ only at $x$, and put
\[
\alpha_i=\alpha_S(x_i),\qquad T=\sum_{i=0}^{m}\alpha_i=s_1.
\]
Whenever a statement uses both endpoints, assume $m\ge1$. The single-vertex path is handled separately in each global bound.

'''+block('thm:lower')

incidence=r'''\section{The exact square census}\label{sec:incidence}
\begin{theorem}[Exact square identity]\label{thm:exact-square}
For every nontrivial snake in $\Q_9$,
\begin{equation}\label{eq:exact-square}
T+2s_0+35v=9214.
\end{equation}
In particular, $T+35v\le9214$.
\end{theorem}
\begin{proof}
The cube has $\binom92 2^7=4608$ coordinate squares, and each vertex belongs to $\binom92=36$ of them. No square has four selected vertices, since these would form a cycle in the induced path. Counting squares and then incidences between selected vertices and squares gives
\[
s_0+s_1+s_2+s_3=4608,\qquad s_1+2s_2+3s_3=36v.
\]
A square with three selected vertices has a unique selected corner adjacent to the other two. That corner is an internal path vertex. Conversely, the two neighbors of each internal path vertex determine a unique coordinate square with three selected vertices; its fourth corner must be absent. These two assignments are inverse, so $s_3=v-2$. Subtracting twice the first census equation from the second yields
\[
-2s_0-s_1+s_3=36v-9216.
\]
Substitute $s_1=T$ and $s_3=v-2$ and rearrange. The inequality follows from $s_0\ge0$.
\end{proof}

The identity states exactly what is lost when empty squares are discarded. A stronger lower estimate for $T$ improves the bound only to the extent allowed by the remaining square census. Section~\ref{sec:empty-packing} assigns some of the term $2s_0$ to selected vertices and retains it in the same argument.

\subsection{Positive singleton counts and endpoint contributions}
The lower estimates used in the global proof require the induced-path condition, including its restriction to two endpoints. The following proofs give these estimates directly. In coordinate expressions such as $ij$ or $aij$, juxtaposition means the sum of the corresponding distinct unit vectors in $\mathbb F_2^9$.

'''+block('lem:one-square')+block('thm:endpoint-four')+r'''
The endpoint estimate does not extend as a lower bound of two to every internal vertex. Theorem~\ref{thm:square-counterexample} gives a 137-edge snake with an internal count equal to one. The explicit witness and its verification are retained in the appendices.

\subsection{Reading a singleton count from missing corners}
'''+block('lem:window-missing-corners')

cycles=between('\\subsection{Cycle constraints beyond four-cycles}', '\\section{Computational investigations and their exact scope}')
cycles=cycles.replace('\\subsection{Cycle constraints beyond four-cycles}','\\subsection{Acyclicity as a finite restriction}')
cycles=cycles[:cycles.index('The lemma and the validity')]+ 'The lemma justifies every finite cycle exclusion used below.\n\n'
finite=r'''\section{From local exclusions to the bound 238}\label{sec:upper-proof}
\subsection{Normalization and necessary local conditions}
A finite transition word is normalized by replacing its distinct coordinate labels, in order of first appearance, by $0,1,2,\ldots$. This replacement extends to a permutation of all nine coordinates. Translation makes its first vertex zero. Both operations preserve adjacency, endpoints, and singleton counts. Reversal permits the same exclusion to be used in either orientation.

For any consecutive block of transitions, the difference between its two end vertices is the sum of the corresponding unit vectors in $\mathbb F_2^9$. The two vertices coincide exactly when every coordinate occurs an even number of times. They are adjacent exactly when one coordinate occurs an odd number of times. These parity tests therefore determine whether a normalized word represents an induced segment: no nonempty block may have zero difference, and a block of length greater than one may not have difference of weight one.

Choose two to five consecutive internal centres and include a Hamming neighborhood containing all corners required to count their singleton squares. A hypothetical snake assigns a selected or unselected value to each represented cube vertex. The following restrictions are necessary:
\begin{enumerate}
\item The prescribed segment vertices are selected. A selected vertex has at most two selected neighbors.
\item Wherever all nine neighbors are represented, a selected vertex has degree one or two. Degree-one vertices in this interior are endpoints of the full snake, so there are at most two.
\item No nonempty set of represented vertices inducing minimum degree at least two is entirely selected.
\item The numbers of missing eligible opposite corners agree with the prescribed singleton counts, by Lemma~\ref{lem:window-missing-corners}.
\end{enumerate}
Boundary vertices do not receive an unjustified degree lower bound: some of their neighbors may lie outside the neighborhood. The conditions are necessary for a full snake; a satisfying local assignment need not extend to one.

'''+cycles+r'''
\subsection{The finite exclusion family}
Represent an internal count $\alpha\ge1$ by $b=\min\{\alpha,6\}$. The symbol six denotes the whole interval $[6,21]$, since there are 21 eligible opposite corners at an internal vertex. It never means an exact count of six unless that equality is explicitly imposed.

Let $\mathcal F$ be the 175 normalized direction-and-count pairs listed in Appendix~\ref{app:exclusion-catalogue}. An occurrence of a listed pair means that its direction word and its clamped internal counts agree with the row, after normalization and possibly reversal.

\begin{lemma}[Finite window exclusions]\label{lem:finite-exclusions}
No window of a snake in $\Q_9$ belongs to $\mathcal F$.
\end{lemma}
\begin{proof}[Computer-assisted proof]
For each row, form the finite Boolean conditions described above in the radius-three neighborhood of its centres. A snake realizing the row supplies values for all selected-vertex variables and for the auxiliary degree, endpoint, and count variables. The count variables can be assigned their actual threshold values; Proposition~\ref{prop:window-counter} proves the equivalence of the threshold clauses and the required counts. Each retained input clause follows from these necessary conditions.

Each of the 175 retained clause sets has a finite contradiction certificate. Its replay checks that every derived clause follows from earlier clauses, ending in the empty clause. The proof checker's soundness gives the following implication: if an assignment satisfied the input, it would satisfy every accepted derived clause. It cannot satisfy the empty clause. Thus the input has no satisfying assignment. The geometric assignment from a hypothetical snake would satisfy that input, giving a contradiction.

Translation, coordinate normalization, the interpretation of every retained clause, the certificate replays, and the assembly over all 175 rows have been checked in Lean. The finite certificates and the state table used next are supplementary proof data in the archived development~\cite{proofarchive}. Their size prevents reproducing every derived clause in print; the exclusion family itself is printed in full.
\end{proof}

\subsection{The potential inequality and its boundary terms}
An induced segment of seven transitions has 34 possible normalized direction words. A state consists of one of these words and the last four clamped internal counts. There are therefore $34\cdot6^4=44064$ states. A permitted transition appends one direction and one count, removes the oldest direction and count, and normalizes the remaining direction word. The eight-direction word must be induced. Every two-, three-, four-, or five-centre window ending at the new centre must avoid $\mathcal F$ in both orientations.

\begin{lemma}[Finite potential certificate]\label{lem:potential-certificate}
There is a nonnegative integer function $\Phi$ on these states, with $\Phi\le15$, such that every permitted transition from a state $u$ to a state $w$, appending count symbol $b$, satisfies
\begin{equation}\label{eq:potential-step}
7+\Phi(w)\le2b+\Phi(u).
\end{equation}
\end{lemma}
\begin{proof}[Finite verification]
The supplementary state table specifies one integer for each state. Its bounds and inequality~\eqref{eq:potential-step} are checked over every eight-direction extension and every five-tuple of count symbols in $\{1,\ldots,6\}$. The direction enumeration includes all normalized induced eight-transition words: their first seven directions belong to the stated 34 shapes, and the appended label is less than nine. Non-induced words and transitions containing a forbidden window impose no inequality. All remaining tests pass by kernel evaluation, in 34 parts indexed by the seven-direction shapes. Coordinate normalization transports the tests to arbitrary coordinate labels. This establishes the stated finite assertion. The bound 15 is the bound used in the checked summation; a tighter table range is unnecessary for the conclusion.
\end{proof}

\begin{lemma}[Sum of the internal singleton counts]\label{lem:internal-total}
For an $m$-edge snake with $m\ge7$,
\begin{equation}\label{eq:internal-total}
7m\le2\sum_{j=1}^{m-1}\alpha_j+52.
\end{equation}
\end{lemma}
\begin{proof}
Index transition directions by $d_0,\ldots,d_{m-1}$, where $d_i$ joins $x_i$ to $x_{i+1}$, and put $b_j=\min\{\alpha_j,6\}$. At index $i$, take the state consisting of $d_i,\ldots,d_{i+6}$ and $b_{i+3},\ldots,b_{i+6}$, and denote its potential by $\Phi_i$. Lemma~\ref{lem:finite-exclusions} ensures that each state transition along the snake is permitted. Hence
\[
7+\Phi_{i+1}\le2b_{i+7}+\Phi_i
\qquad(0\le i\le m-8).
\]
Sum these $m-7$ inequalities. When $m=7$ the sum is empty and the same inequality holds with identical initial and final potentials. Cancellation gives
\[
7(m-7)+\Phi_{m-7}\le2\sum_{j=7}^{m-1}b_j+\Phi_0.
\]
Use $\Phi_{m-7}\ge0$, $\Phi_0\le15$, $b_j\le\alpha_j$, and $\sum_{j=1}^{6}\alpha_j\ge6$ from Lemma~\ref{lem:one-square}. It follows that
\[
7(m-7)\le2\sum_{j=1}^{m-1}\alpha_j-12+15.
\]
Adding 49 yields~\eqref{eq:internal-total}. This includes all initial and terminal losses explicitly.
\end{proof}

\begin{proposition}[Conditional upper bound 238]\label{prop:direction238}
Exclusion of the 175 windows in $\mathcal F$, together with the verified potential table, implies that every snake in $\Q_9$ has at most 238 edges.
\end{proposition}
\begin{proof}
The assertion is immediate for $m<7$. Otherwise the preceding summation uses only these exclusions and the table. Since the two endpoint counts sum to at least eight, it gives
\[
2T\ge7m-36.
\]
The exact square identity, with $v=m+1$, gives $2T+70(m+1)\le18428$. Combining these inequalities yields
\[
77m\le18394<77\cdot239=18403.
\]
Since $m$ is an integer, $m\le238$.
\end{proof}

\begin{theorem}[Verified upper bound 238]\label{thm:upper238}
Every snake in $\Q_9$ has at most 238 edges. Consequently $191\le a(9)\le238$.
\end{theorem}
\begin{proof}
Lemma~\ref{lem:finite-exclusions} supplies all exclusions required by Proposition~\ref{prop:direction238}, and Lemma~\ref{lem:potential-certificate} supplies the table inequality. Apply that proposition and the explicit lower bound in Theorem~\ref{thm:lower}.
\end{proof}

This proof establishes the main interval without using the conjectured value 196, the later share estimates, or any restricted construction search. The certificate audit and the remaining independent-rebuild limitation are stated in Section~\ref{sec:verification}.

'''

# Keep the sharp geometric arguments together, before introducing empty-square shares.
pair=between('\\subsection{Distance-three six-cycle inequalities}', '\\begin{proposition}[Three-square share bonus]')
pair=pair.replace('\\subsection{Distance-three six-cycle inequalities}\\label{sec:distance-three-pair}', '\\section{Sharp restrictions on two singleton counts}\\label{sec:distance-three-pair}')
pair=pair.replace('A small refutation in the preceding classification suggests a direct geometric explanation.', 'The next inequalities follow from explicit six-cycles near two selected vertices.')
pair=pair[:pair.index('Independent square enumeration')]

share=sub('Retaining empty squares through weighted windows','Separating window exclusions from share estimates')
share=share.replace('\\subsection{Retaining empty squares through weighted windows}', '\\section{Retaining empty squares through integer shares}')
share=share.replace('Each internal path vertex contributes exactly one wedge and each endpoint contributes none, so $W=v-2$ in~\\eqref{eq:anchored-square-count}. Hence $T+2s_0+35v=9214$.', 'Theorem~\\ref{thm:exact-square} gives $T+2s_0+35v=9214$.')
share=share.replace('The integer identity and the displayed global inequality have been checked in Lean. The corner-share construction and its geometric interpretation were developed in the parallel upper-bound work; the exact remainder identity records the loss explicitly.', 'The identity and its geometric interpretation have been checked in Lean. In particular, no positive contribution is assigned to an empty corner with no selected neighbor.')
diagshare=share[share.index('In saved radius-four computations'):share.index('\\begin{proposition}[Explicit charge targets]')]
targets=share[share.index('\\begin{proposition}[Explicit charge targets]'):]
share=share[:share.index('In saved radius-four computations')]
bonus=between('\\begin{proposition}[Three-square share bonus]', '\\subsection{Joint consistency of mixed-count windows}')
diagpair=bonus[bonus.index('The diagnostic graph needs'):]
bonus=bonus[:bonus.index('The diagnostic graph needs')]
share+='\\subsection{A forced three-square contribution}\n'+bonus
share+=r'''Independent square enumeration on the sharpness witnesses of Proposition~\ref{prop:pair-sharpness} gives share pairs $(48,29)$ and $(25,17)$ at $M=12$. Their two-position charges are $317$ and $258$. These values are checks of particular witnesses and do not establish the minimum charge.

'''

# Retain proved overlap statements, and put diagnostic state histories in an appendix.
direct=sub('Separating window exclusions from share estimates','Overlap consistency and selective history')
direct_proof=block('prop:share-window-exclusion')
diagdirect=direct.replace(direct_proof.strip(),'See Proposition~\\ref{prop:share-window-exclusion} for the proved exclusion.\n\n')
overlap=sub('Overlap consistency and selective history','Recovering the excess hidden by a coarse count')
seven=block('prop:seven-overlap')
diagoverlap=overlap.replace(seven.strip(),'The four patterns are excluded by Proposition~\\ref{prop:seven-overlap}.\n\n')
coarse=sub('Recovering the excess hidden by a coarse count','A candidate restriction on consecutive counts of four')
diagcoarse=between('\\paragraph{Diagnostic effect and stronger experimental targets.}', '\\begin{proposition}[Joint singleton excess]')
coarse=coarse.replace(diagcoarse,'')
four=sub('A candidate restriction on consecutive counts of four','Distance-three six-cycle inequalities')
mixed=sub('Joint consistency of mixed-count windows','Overlapping endpoint demands')
mixed_proof=block('prop:mixed-overlap')
diagmixed=mixed.replace(mixed_proof,'The two checked exclusions are stated in Proposition~\\ref{prop:mixed-overlap}.\n\n')
joint=r'''\section{Compatibility between overlapping windows}\label{sec:compatibility}
A local model for one window may have a solution that disagrees with every solution for its neighboring window on their shared vertices. The following exclusions impose the counts on a common selected-vertex set. They strengthen necessary conditions on snakes, although a global aggregate improvement still requires coverage of all permitted sequences.

\subsection{An ordinary five-centre exclusion}\label{sec:direct-share}
'''+direct_proof+r'''
\subsection{Seven centres with equal counts}\label{sec:share-overlap}
For the five-centre shapes
\[
A=(0,1,2,3,0,4),\qquad B=(0,1,2,3,0,1),
\]
three consecutive windows consisting of two copies of $A$ and one of $B$, up to normalization and reversal, reduce to the four patterns in the following proposition. This gives a concrete compatibility restriction stronger than separate treatment of each five-centre window.

'''+seven+coarse+r'''
\subsection{Seven centres with mixed counts}\label{sec:critical-overlap}
'''+mixed_proof+r'''
These two exclusions were selected from periodic sequences admitted by a weaker diagnostic model. They eliminate those particular sequences. The modified model admits a replacement sequence at the same saved lower-table mean, so this result alone yields no improvement of Theorem~\ref{thm:upper238}. The computations and their precise scope are recorded in Appendix~\ref{app:diagnostics}.

'''
joint=joint.replace('Both currently recorded diagnostic cycles avoid these qualifying windows, so stronger weights at these positions alone do not eliminate those cycles.', 'The saved diagnostic cycles in Appendix~\\ref{app:diagnostics} avoid these qualifying windows. Increasing only these weights therefore leaves those particular cycles admissible.')

demands=sub('Overlapping endpoint demands','The exact optimum')
density=sub('A limitation of uniform singleton-density estimates','Retaining empty squares through weighted windows')
closure=r'''\section{What a stronger upper bound still requires}\label{sec:closure}
The established local inequalities can enter a global proof only through an accounting rule that prevents repeated use of the same contribution. Lemma~\ref{lem:share-packing}, the multiplicity bounds for count excess, and Corollary~\ref{cor:occurrence-share} supply such rules. A positive density of the relevant configurations, or a finite potential covering every allowed alternative, is still required.

\subsection{Sufficient charge inequalities}
'''+targets+four+demands+density
closure=closure.replace('The successive diagnostic cycles repeatedly contain counts equal to four. This suggests a direction-independent restriction.', 'A direction-independent exclusion of six consecutive counts equal to four would replace several special direction cases by one restriction on the count sequence.')

optimal=sec('Exact targets for an optimality proof','Witnesses, endpoint obstruction, and an invalid inference')
optimal=optimal.replace('\\section{Exact targets for an optimality proof}', '\\section{Construction and the requirements for optimality}\\label{sec:optimality}\n\\subsection{The next-length criterion}')
blocking=sec('Witnesses, endpoint obstruction, and an invalid inference','A global upper bound').replace(block('thm:lower'),'')
blocking=blocking.replace('\\section{Witnesses, endpoint obstruction, and an invalid inference}','\\subsection{Endpoint maximality and maximum length}')
cycleconstruct=demote(sec('Cycles as an alternative construction route','The two-layer construction and its obstruction'))
layer=demote(sec('The two-layer construction and its obstruction','Independent hypothesis from the first eight terms'))
layersearch=layer[layer.index('The length-98 seed in Appendix'):]
layer=layer[:layer.index('The length-98 seed in Appendix')]+r'''The explicit compatible paths of lengths 96 and 94 in Appendix~\ref{app:joint-seed} give a 191-edge construction of this form. Restricted tests with a fixed 98-edge seed are described in Appendix~\ref{app:experiments}; their failure does not exclude other seeds or multiple-crossing paths.

'''
hypothesis=between('\\section{Independent hypothesis from the first eight terms}', '\\subsection{A restriction on one-singleton configurations}')
hypothesis=hypothesis.replace('\\section{Independent hypothesis from the first eight terms}', '\\section{A numerical conjecture and its limitations}\\label{sec:hypothesis}')
hypothesis=hypothesis.replace('it is not used in any proof below', 'it is not used in any theorem in this paper')

verification=r'''\section{Verification status and unresolved questions}\label{sec:verification}
The mathematical claims have different evidential scopes. Explicit transition sequences give existence statements only after all distinctness and adjacency conditions have been checked. A local exclusion requires a geometric interpretation of its input conditions as well as a sound contradiction certificate. A global upper bound additionally requires coverage of every relevant window and an aggregation argument with endpoint terms. The proof of Theorem~\ref{thm:upper238} follows this complete dependency chain.

The 191-edge witness, the geometric counting lemmas, and the assembled 241-edge theorem have successful Lean checks. The 241 proof, including its 22 local refutations, has source-build and final dependency-audit receipts on two platforms. The stronger 238 theorem has a successful final dependency audit on Linux against an incrementally built library. Its audited dependencies are propositional extensionality, classical choice, and quotient soundness. An independent rebuild of the complete 238 proof in a fresh directory remains pending. This reproducibility limitation must be distinguished from a missing mathematical hypothesis: the assembled theorem has discharged all 175 window premises.

The 175 refutations contain about 4.6 million derived clauses and 270 million antecedent references. Their replay was divided into 2803 kernel checks, using about 40 kernel-hours in total, with at most 4~GB per check. These figures describe the recorded verification; they do not substitute for the soundness argument. For 56 windows, alternative refutations of the same inconsistent core were used. Each was checked under the same logical rules.

The sharp pair inequalities, their sharpness witnesses, the three-square bonus, the weighted accounting results, and the two mixed-count exclusions have also passed their stated Lean checks. Numerical searches elsewhere in the paper retain their narrower labels. In particular, an unresolved solver run proves neither feasibility nor impossibility; a local forest proves feasibility only in its local model; and an exact mean of one saved state cycle is not a certificate of the minimum over all cycles.

The exact optimum remains unresolved. No 192-edge construction has been obtained in the work reported here, and no universal exclusion of length 192 has been established. For the empty-square approach, the principal remaining obligation is a verified lower estimate for $G_{12}$ on every snake, including all alternatives to the currently charged patterns. For construction, the joining and contraction criteria identify valid search families, but the restricted failures do not exclude their complements. The conjecture $a(9)=196$ remains compatible with the proved interval and requires both a 196-edge construction and a 197-edge exclusion.

\appendix
\section{Geometric restrictions and intermediate bounds}\label{app:geometry}
This appendix retains the detailed geometric arguments supporting the simpler count restrictions. The main proof uses the direct positivity and endpoint proofs from Section~\ref{sec:incidence}. The intermediate bounds explain the consequences of additional local information. The long three-count classification is a checked finite proof whose printed account is an outline; it is identified as such wherever individual branches are omitted.

'''
huang=demote(sec('A global upper bound','Square faces and the role of endpoints'))
sq=demote(sec('Square faces and the role of endpoints','Adjacent singleton minima and the bound 251')).replace(block('lem:one-square'),'')
sq=sq.replace('For a vertex set $S\\subseteq\\Q_9$ and $x\\in S$, let $\\alpha_S(x)$ be the number of two-dimensional coordinate faces whose intersection with $S$ is exactly $\\{x\\}$. Such a face will be called a singleton square at $x$. ', '')
geo=between('\\section{Adjacent singleton minima and the bound 251}', '\\section{Cycles as an alternative construction route}')
geo=demote(geo.replace(block('thm:endpoint-four'),''))
split=between('\\subsection{A restriction on one-singleton configurations}', '\\subsection{Cycle constraints beyond four-cycles}')
condition=sub('A conditional strengthening','Local experiments on the pattern $(2,2,3)$')
condition=condition.replace('The next proposition records an intermediate implication. Its local premise is now established by the window argument below, which gives the stronger bound in Theorem~\\ref{thm:main}.', 'The next proposition records an intermediate implication whose local premise is included in the checked exclusion family. The main theorem gives a stronger consequence of the larger family.')
oldaggregate=sub('The aggregate limit of local windows and the bounds 242 and 241','A limitation of uniform singleton-density estimates')
oldaggregate=oldaggregate[:oldaggregate.index('\\begin{proposition}[Conditional upper bound 238]')]
oldaggregate=oldaggregate.replace('The same local model can be used for every count pattern. It indicates how far the potential method can go.', 'The following smaller finite models explain the intermediate bounds. They are retained separately from the direct proof of 238 in Section~\\ref{sec:upper-proof}.')
oldaggregate=oldaggregate.replace('The stronger direction-aware exclusions discussed next now have their own successful proof audit.', 'The larger direction-aware family used in Section~\\ref{sec:upper-proof} has its own successful proof audit.')

threshold=r'''\section{Threshold clauses for exact counts}\label{app:counters}
The following elementary equivalence supplies the auxiliary counting variables used in finite window models. It concerns the truth values of the represented conditions and does not assume that a local assignment extends to a snake.

'''+block('prop:window-counter')

# Print the complete finite set; derive it from the same pinned source as the proof.
key_source=(ROOT/'work/final_lean/LocalWindowDirKeys5.lean').read_text(encoding='utf-8')
key_part=key_source.split('def dirKeys5 :')[1].split(']\n')[0]
keys=[(list(map(int,re.findall(r'\d+',a))),list(map(int,re.findall(r'\d+',b)))) for a,b in re.findall(r'\(\[([^]]+)\], \[([^]]+)\]\)',key_part)]
assert len(keys)==175
catalogue=r'''\section{The complete exclusion catalogue for 238}\label{app:exclusion-catalogue}
The table specifies $\mathcal F$ from Lemma~\ref{lem:finite-exclusions}. A direction word lists successive flips, normalized by first appearance. A count word lists the counts at the internal centres, in the same order. Digits 1 through 5 are exact counts; digit 6 means any count from 6 through 21. For a direction word of length $k+1$, the count word has length $k$. Each row is excluded together with its reversed and renormalized form. The latter forms need not be printed again.

\begin{longtable}{rll}
\caption{The 175 forbidden direction-and-count pairs.}\label{tab:exclusion-catalogue}\\
\toprule
Row & Direction word & Count word\\
\midrule
\endfirsthead
\toprule
Row & Direction word & Count word\\
\midrule
\endhead
\bottomrule
\endfoot
'''
catalogue+=''.join(f"{i} & $({','.join(map(str,ds))})$ & $({','.join(map(str,cs))})$\\\\\n" for i,(ds,cs) in enumerate(keys,1))
catalogue+='\\end{longtable}\n\n'

experiments=sec('Computational investigations and their exact scope','Formal verification and further questions')
experiments=experiments.replace('\\section{Computational investigations and their exact scope}', r'\section{Construction experiments and their scope}\label{app:experiments}'+'\nThe experiments below record the tested search spaces and their outcomes. Their exclusions apply only to the stated fixed boundaries, templates, or resource-limited runs. They supply no additional premise in the proof of the global interval.\n')
experiments+='\\subsection{Fixed-seed two-layer tests}\n'+layersearch
localexperiments=sub('Local experiments on the pattern $(2,2,3)$','The aggregate limit of local windows and the bounds 242 and 241')
localexperiments=localexperiments.replace(block('lem:window-missing-corners'),'').replace(block('prop:window-counter'),'')
localexperiments=localexperiments.replace('the separate complete window proof below', 'the complete window proof in Section~\\ref{sec:upper-proof}')
localexperiments=localexperiments.replace('The separate window proof below establishes', 'The window proof in Section~\\ref{sec:upper-proof} establishes')

diagnostics=r'''\section{Local-model diagnostics and incomplete searches}\label{app:diagnostics}
The tables in this appendix are research diagnostics. A recorded local-witness value is an attainable value for one local assignment. A recorded lower-table value has the verification status stated with it. The mean of a saved cycle is checked by exact arithmetic, but this does not prove that it is the least mean of all cycles. None of the diagnostic means is used as a universal lower bound for snakes in this paper.

\subsection{Packing numerical window estimates}
'''+diagshare+diagdirect+diagoverlap+diagcoarse+'\\subsection{Pair inequalities in the diagnostic graph}\n'+diagpair+diagmixed+localexperiments
# The main sections own these cross-reference labels.
for label in ('sec:direct-share','sec:share-overlap','sec:critical-overlap'):
    diagnostics=diagnostics.replace('\\label{'+label+'}','')
diagnostics=diagnostics.replace('The exclusions and the resulting correction are established below.', 'The exclusions and the correction are established in Section~\\ref{sec:coarse-excess}.')
diagnostics=diagnostics.replace('The two saved critical cycles in the preceding diagnostic calculation', 'The two saved critical cycles after the pair-inequality update')

original_appendices=between('\\section{Explicit transition sequences and blockers}', '\\begin{thebibliography}')
original_appendices=original_appendices.replace('The second sequence in', 'The 93-edge sequence in')
bibliography=old[old.index('\\begin{thebibliography}'):]
bibliography=bibliography.replace('\\end{thebibliography}', r'\bibitem{proofarchive} I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Snake-in-the-box in dimension nine: proof certificates and research record}. Archived repository state, 23 October 2026. \url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/ffdf1b94403396a1b8ddaffdae419bb897ba5cf8}.'+'\n\\end{thebibliography}')
parts=[preamble,abstract,intro,main,incidence,finite,pair,share,joint,closure,optimal,blocking,cycleconstruct,layer,hypothesis,verification,huang,sq,geo,split,condition,oldaggregate,threshold,catalogue,experiments,diagnostics,original_appendices,bibliography]
new=''.join(parts)
# Remove chronology-dependent references whose destinations moved.
new=new.replace('The second sequence in Appendix~\\ref{app:witness}', 'The 93-edge sequence in Appendix~\\ref{app:witness}')
new=new.replace('stated in Section~1', 'stated in Section~\\ref{sec:problem}')
new=new.replace('with counts above six identified', 'with counts at least six represented by one symbol')
new=new.replace('counts (with counts above six identified)', 'counts (with counts at least six represented by one symbol)')
new=new.replace('The residual deductions complete the formal classification outlined here.', 'The residual deductions complete the checked classification outlined here.')
new=new.replace('the unconditional bound 241 established below', 'the unconditional bound 238 in Theorem~\\ref{thm:upper238}')
new=new.replace('Only the two displayed phase exclusions are asserted as theorems here;', 'Only the two phase exclusions in Proposition~\\ref{prop:mixed-overlap} are asserted as theorems here;')
new=new.replace('the four patterns displayed above. The finite classification', 'the four patterns of Proposition~\\ref{prop:seven-overlap}. The finite classification')
new=re.sub(r'\n{4,}', '\n\n\n',new)
new='\n'.join(s.rstrip() for s in new.splitlines())+'\n'
paper=ROOT/'paper/snake9_research.tex'
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
paper.write_text(new,encoding='utf-8',newline='\n')
editor.write_bytes(paper.read_bytes())
(HERE/'data').mkdir(exist_ok=True)
(HERE/'data/exclusion-catalogue.json').write_text(json.dumps(keys,indent=2)+'\n')
print('Rewrote existing paper:',len(old),'->',len(new),'characters;',len(keys),'catalogue entries')

if __name__=='__main__':
    pass
