"""Add the audited 236 theorem while retaining the rewritten argument and settings."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
p=ROOT/'paper/snake9_research.tex';s=p.read_text(encoding='utf-8')
assert r'\label{thm:upper236}' not in s
a=s.index(r'\begin{abstract}');b=s.index(r'\end{abstract}',a)
s=s[:a]+r'''\begin{abstract}
Let $a(9)$ be the maximum number of edges in an induced path of the nine-dimensional binary hypercube. The results assembled here establish $191\le a(9)\le236$. The lower bound is a published construction, reproduced as an explicit transition sequence. The upper bound follows from the exact identity $T+2s_0+35v=9214$, where $v$ is the number of selected vertices, $T$ is the total number of singleton squares, and $s_0$ is the number of empty squares. A finite family of 175 forbidden windows first yields the bound 238. A radius-four family of 732 forbidden windows strengthens the potential inequality to $11T\ge42(v-1)-203$, giving 236. The proof separates the geometric interpretation of each window, the checked finite refutations, the potential table, and the summation with endpoint terms. Further results retain the empty-square term through integer shares, prove sharp distance-three inequalities and asymmetric distance-four restrictions, and establish a three-square share bonus and overlap exclusions. These refinements do not yet give a smaller uniform bound. Explicit counterexamples distinguish endpoint maximality and local feasibility from global optimality. The value 196 remains a numerical conjecture. The complete 236 theorem has a successful Lean dependency audit against an incrementally built Linux library; an independent rebuild remains pending.
'''+s[b:]
s=s.replace(r'\boxed{191\le a(9)\le238.}',r'\boxed{191\le a(9)\le236.}',1)
s=s.replace('The upper bound is deduced in Section~\\ref{sec:upper-proof}.','The upper bound is deduced in Theorem~\\ref{thm:upper236}. Section~\\ref{sec:upper-proof} first develops the argument for 238 and then proves its radius-four strengthening to 236.',1)
s=s.replace(r'\section{From local exclusions to the bound 238}',r'\section{From local exclusions to the bounds 238 and 236}',1)
s=s.replace('This proof establishes the main interval without using the conjectured value 196, the later share estimates, or any restricted construction search.','This first bound uses neither the conjectured value 196 nor the later share estimates or restricted construction searches. The next refinement uses the same counting identity and a stronger exclusion family.',1)
section=r'''
\subsection{The radius-four refinement to 236}\label{sec:radius-four-236}
Replace the radius-three neighborhood by the union of the Hamming balls of radius four around the prescribed centres. Retain the same count symbols, state representation, normalization, and necessary degree, endpoint, and acyclicity conditions. Let $\mathcal F_4$ be the family of 732 normalized direction-and-count pairs in the supplementary catalogue~\cite{radiusfourarchive}. Each pair specifies two to five consecutive internal centres, with the symbol six still representing the interval $[6,21]$. The catalogue, its geometric interpretation, and the potential table are fixed proof data.

\begin{lemma}[Radius-four exclusions and potential]\label{lem:radius-four-certificate}
No window of a snake in $\Q_9$ belongs to $\mathcal F_4$. There is a nonnegative integer potential $\Psi$ on the same 44064 states, bounded above by 63, such that every induced state transition avoiding $\mathcal F_4$, with appended count symbol $b$, satisfies
\begin{equation}\label{eq:radius-four-step}
42+\Psi(w)\le11b+\Psi(u).
\end{equation}
\end{lemma}
\begin{proof}[Computer-assisted proof]
For each of the 732 rows, a hypothetical occurrence is translated and its coordinates are permuted to the canonical window. Restricting the snake to the radius-four neighborhood provides a selected-vertex assignment. The missing-corner identity gives the specified count variables; actual degrees and endpoint indicators give the remaining auxiliary variables. The degree conditions follow from the induced-path definition, and Lemma~\ref{lem:subset-low-degree} justifies each retained cycle exclusion. Thus every retained input clause is satisfied by this assignment. A resolution refutation of that input, replayed through the sound proof checker described above, ends in the empty clause. The resulting contradiction excludes the row. The arbitrary-window reduction, clause implications, all 732 refutations, and their assembly have passed the recorded Lean checks~\cite{radiusfourarchive}.

The potential is specified by an integer at each state. There are 34 normalized induced seven-direction shapes and 132 normalized induced eight-direction shapes. Checking each of the latter against all $6^5$ count choices covers $1\,026\,432$ candidate transitions. Discard nonpermitted transitions and verify~\eqref{eq:radius-four-step} for each remaining transition. The kernel checks this assertion in 34 parts. A separate enumeration made for this revision verifies the same inequality for all 611613 permitted transitions and finds potential values between zero and 48. The bound 63 stated here is the weaker bound used by the Lean summation, and is sufficient. The independent enumeration verifies the potential assertion only; the window exclusions are supplied by the preceding proof certificates.
\end{proof}

\begin{proposition}[Radius-four internal count sum]\label{prop:radius-four-sum}
For every $m$-edge snake with $m\ge7$,
\begin{equation}\label{eq:radius-four-sum}
42m\le11\sum_{j=1}^{m-1}\alpha_j+291.
\end{equation}
\end{proposition}
\begin{proof}
Use the states indexed by $i$ in the proof of Lemma~\ref{lem:internal-total}, and let $\Psi_i$ be their new potentials. The exclusion assertion in Lemma~\ref{lem:radius-four-certificate} makes every state transition along the snake permitted. Sum~\eqref{eq:radius-four-step} over $0\le i\le m-8$ to obtain
\[
42(m-7)+\Psi_{m-7}\le11\sum_{j=7}^{m-1}b_j+\Psi_0.
\]
For $m=7$ the sum is empty and the same assertion holds. Since $\Psi_{m-7}\ge0$, $\Psi_0\le63$, $b_j\le\alpha_j$, and the first six internal counts sum to at least six,
\[
42(m-7)\le11\sum_{j=1}^{m-1}\alpha_j-66+63.
\]
Adding 294 gives~\eqref{eq:radius-four-sum}; in particular, its boundary constant is $294-66+63=291$.
\end{proof}

\begin{theorem}[Verified upper bound 236]\label{thm:upper236}
Every snake in $\Q_9$ has at most 236 edges. Consequently $191\le a(9)\le236$.
\end{theorem}
\begin{proof}
If $m<7$, the assertion is immediate. Otherwise both endpoint counts are at least four, so Proposition~\ref{prop:radius-four-sum} gives
\[
42m\le11(T-8)+291=11T+203.
\]
The exact square identity and $s_0\ge0$ imply $11T+385(m+1)\le101354$. Combining the two inequalities yields
\[
427m\le101172<427\cdot237=101199.
\]
The integer $m$ is therefore at most 236. The lower bound follows from Theorem~\ref{thm:lower}.
\end{proof}

All 732 local premises of this theorem have been discharged in the archived development. The recorded build and the independent checks made for this revision have different scopes, detailed in Section~\ref{sec:verification}. The theorem still discards $s_0$; the subsequent share estimates retain information omitted from this bound.

'''
anchor=r'\section{Sharp restrictions on two singleton counts}'
s=s.replace(anchor,section+anchor,1)
s=s.replace('The proof of Theorem~\\ref{thm:upper238} follows this complete dependency chain.','The proofs of Theorems~\\ref{thm:upper238} and~\\ref{thm:upper236} follow this complete dependency chain.',1)
anchor='The sharp distance-three inequalities, their sharpness witnesses,'
insert=r'''The stronger 236 theorem has a recorded successful Linux audit in the pinned contributor development~\cite{radiusfourarchive}. Its final existence-and-upper-bound theorem uses the same snake definition and lists only propositional extensionality, classical choice, and quotient soundness. The saved replay summary reports all 732 refutations completed, with 7190 kernel checks across the reused and new refutations and approximately 100 kernel-hours. These totals concern the whole 732-window family. The local copy added for this revision preserves selected proof interfaces, the complete exclusion catalogue, and the audit receipts; it does not claim a fresh local rebuild of that complete dependency chain. The independent potential enumeration and four new Lean checks verify the arithmetic of the printed summation and final bound, conditional on the stated window and table premises. They supplement the contributor's complete audit. A clean independent rebuild of the full 236 theorem remains a reproducibility task.

'''
s=s.replace(anchor,insert+anchor,1)
s=s.replace(r'current interval $191\le a(9)\le238$',r'current interval $191\le a(9)\le236$')
s=s.replace(r'The window proof in Section~\ref{sec:upper-proof} establishes the current interval',r'The radius-four refinement in Section~\ref{sec:upper-proof} establishes the current interval')
bib=r'''\bibitem{radiusfourarchive}
Snake-in-the-box project contributors, radius-four proof archive, revision \texttt{7cb52aad}, 24 October 2026. The pinned sources, final theorem, and Linux replay and dependency-audit receipts are available at
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b}.

'''
s=s.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
p.write_text(s,encoding='utf-8',newline='\n')
Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').write_bytes(p.read_bytes())
print('Updated the repository paper and existing editor source.')
