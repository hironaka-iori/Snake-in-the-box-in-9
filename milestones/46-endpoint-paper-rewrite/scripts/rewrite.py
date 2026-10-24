"""One-time revision of the complete manuscript after research round 45."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
paper=ROOT/'paper/snake9_research.tex'
BASE='c0a672d7d314317bf69332fc7029e00853e16b04'
old=subprocess.check_output(['git','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode('utf-8').replace(r'\r\n','\n')
assert editor.read_text(encoding='utf-8')==paper.read_text(encoding='utf-8')==old
s=old
def replace(a,b):
    global s
    assert s.count(a)==1,(a[:120],s.count(a))
    s=s.replace(a,b,1)

abstract=r'''Let $a(9)$ be the maximum number of edges in an induced path in the nine-dimensional binary hypercube. The verified interval assembled here is $191\le a(9)\le236$. We present the upper-bound argument from the square census through the local exclusions, finite potential, and endpoint summation. Its counting identity is $T+2s_0+35v=9214$, where $v$ counts path vertices, $T$ counts singleton squares, and $s_0$ counts empty squares. We then develop three refinements: inequalities between local singleton counts, integer shares of empty squares, and a common budget for overlapping count excesses. For the eight-transition pattern $(a,b,c,d,e,a,d,b)$ with distinct named coordinates, the counts at offsets two and six sum to at least seven. Equality forces an endpoint at Hamming distance two from the first counted vertex; excluding endpoints within that distance raises the sharp bound to eight. Complete snakes attain both constants. The enlarged finite model still has exact normalized minimum cycle mean $42/11$, so these refinements do not yet improve the global bound. Construction criteria, counterexamples, and restricted searches delimit the remaining problem. The value 196 is an extrapolation, with no construction or optimality proof. The archived complete 236 proof has a successful Lean dependency audit; an independent full rebuild remains pending.'''
start=s.index(r'\begin{abstract}')+len(r'\begin{abstract}');end=s.index(r'\end{abstract}')
s=s[:start]+'\n'+abstract+'\n'+s[end:]

# Define the quantities before stating the principal theorem and its roadmap.
start=s.index('For a snake $P=(x_0,');end=s.index(r'\begin{theorem}[Verified lower bound]',start)
notation=s[start:end];s=s[:start]+s[end:]
at=s.index(r'\begin{theorem}[Main result]')
s=s[:at]+r'\subsection{Counting notation}'+'\n'+notation+r'\subsection{Results and proof dependencies}'+'\n'+s[at:]
replace(r'The subsequent sections investigate the information omitted by that bound. Pair inequalities restrict which singleton counts can coexist; integer shares retain some empty-square contributions; and joint-window restrictions recover count excess lost by truncation. Section~\ref{sec:common-budget} combines these contributions under one overlap rule and identifies the obstruction that survives in the resulting finite model. Construction criteria and the numerical conjecture are treated separately, since neither supplies a premise for the upper-bound proof. Detailed earlier bounds, finite catalogues, and restricted search records are retained in the appendices.',r'''The rest of the argument separates local geometry from its aggregate consequences. Section~\ref{sec:distance-three-pair} proves pair inequalities. Section~\ref{sec:endpoint-pair} identifies the endpoint configuration required when a further pair inequality is sharp. Integer shares in Section~\ref{sec:empty-packing} preserve part of the empty-square term, and the joint restrictions in Section~\ref{sec:compatibility} control counts that cannot coexist on one selected set. Section~\ref{sec:common-budget} combines count excess and shares with explicit multiplicity bounds. The resulting finite-model computation identifies a surviving obstruction; it supplies no improved global theorem. The numerical hypothesis and construction criteria follow after these deductions. The appendices preserve earlier proofs, complete witness sequences, finite catalogues, and experiments with their precise scopes.''')
replace(r'Further local inequalities & The stated geometric hypotheses and checked local proofs; they do not yet lower 236.\\',r'Pair bounds seven and eight & Complete Lean checks, explicit sharpness witnesses, and an endpoint-distance criterion.\\')
replace(r'Finite-model mean $42/11$ & An attaining cycle and an integer potential checked on every retained edge of the saved graph.\\',r'Finite-model mean $42/11$ & A cycle and an integer potential checked on every edge, including after the sharp pair restriction.\\')

# Put the endpoint-demand theorem immediately after the other sharp pair results.
new=r'''
\section{A sharp pair inequality and its endpoint obstruction}\label{sec:endpoint-pair}
The neighboring transitions around two counted vertices can change the best possible inequality. The next result uses the full eight-transition segment. Its equality case also identifies a specific endpoint demand, which explains why distance from the endpoints permits a stronger bound.

\begin{theorem}[Outer-transition pair bound]\label{thm:outer-pair}
Let $P=(x_0,\ldots,x_m)$ be a snake and let $r+8\le m$. If its eight transitions starting at $x_r$ are
\[
(a,b,c,d,e,a,d,b),
\]
where the five named coordinates are distinct, then
\[
\alpha_{r+2}+\alpha_{r+6}\ge7.
\]
The constant seven is best possible under these hypotheses.
\end{theorem}
\begin{proof}[Computer-assisted proof and explicit sharpness]
Translate $x_r$ to zero and send $(a,b,c,d,e)$ to $(0,1,2,3,4)$. The segment becomes
\[
(0,1,3,7,15,31,30,22,20).
\]
Its counted vertices are 3 and 30. Their difference has four nonzero binary digits. At each centre, the two prescribed path neighbors exclude two coordinates from its singleton-square count. List the 21 opposite corners from the other seven coordinates, and concatenate the two lists. By Lemma~\ref{lem:window-missing-corners}, the number of absent entries, with multiplicity, equals $\alpha_{r+2}+\alpha_{r+6}$.

Suppose that sum is at most six. In the radius-four neighborhood of the internal centres, impose this joint upper bound together with the necessary degree, endpoint, square-cycle, and six-cycle restrictions of Section~\ref{sec:upper-proof}. A snake realizing the segment supplies the selected-vertex assignment and its actual endpoint indicators; the threshold variables are assigned their actual partial counts. The retained input has 1076 clauses on 879 variables. A refutation with 594 derived clauses and 34159 antecedent references derives the empty clause. Its replay, the interpretation of each retained clause, and the invariance of both singleton counts under the normalization have passed Lean~\cite{outerpairarchive}. The assumed sum is therefore impossible. No hypotheses on the other five counts enter the proof.

The 140-edge snake in Appendix~\ref{app:endpoint-witnesses} has this segment at $r=2$, with $(\alpha_4,\alpha_8)=(4,3)$. Distinctness, induced adjacency, the segment, and both counts have passed Lean. Its sum is seven, proving sharpness.
\end{proof}

The two outer transitions cannot both be omitted while retaining this bound. Deleting them leaves, after coordinate renaming, the six-transition pattern $(0,1,2,3,4,2)$, with the counted positions now at offsets one and five. The 146-edge snake in Appendix~\ref{app:endpoint-witnesses} realizes that shorter pattern with counts $(3,3)$. Its Lean-checked sum is six. Thus the full segment in Theorem~\ref{thm:outer-pair} is an essential part of the stated result.

\subsection{The endpoint demand set}
For the same eight-transition segment, put $x=x_{r+2}$ and
\[
F=\{0,\ldots,8\}\setminus\{b,c\},\qquad
G_r=\left\{x+e_i+e_j:
\{i,j\}\in\binom F2\setminus\bigl\{\{a,e\},\{d,e\}\bigr\}\right\}.
\]
Here addition is in $\mathbb F_2^9$. The set $F$ consists of the seven directions unused by the path at $x$. Its 21 coordinate pairs give distinct opposite corners, and the two removed pairs are distinct, so $|G_r|=19$. Every member of $G_r$ is at Hamming distance two from $x$.

In the normalized segment, the removed corners are 18 and 27. The vertex 18 is adjacent to the internal vertex 22, whose segment neighbors are 30 and 20. The vertex 27 is adjacent to the internal vertex 31, whose segment neighbors are 15 and 30. Each removed corner would therefore give an internal vertex a third selected neighbor. Both are absent. The demand set consists of the remaining eligible opposite corners.

\begin{theorem}[Endpoint demand at equality]\label{thm:endpoint-demand}
Under the hypotheses of Theorem~\ref{thm:outer-pair}, if
\[
\alpha_{r+2}+\alpha_{r+6}\le7,
\]
then $G_r$ contains an endpoint of $P$. In particular,
\[
\Ham(x_{r+2},x_0)=2\quad\text{or}\quad
\Ham(x_{r+2},x_m)=2.
\]
\end{theorem}
\begin{proof}[Computer-assisted proof]
Normalize the segment as in Theorem~\ref{thm:outer-pair}. Its first counted vertex is 3. The set $G_r$ becomes
\[
\{10,34,43,51,66,75,83,99,130,139,147,163,195,
258,267,275,291,323,387\}.
\]
Assume that none of these 19 vertices is an endpoint. Assign an endpoint indicator to every represented vertex, true precisely at an endpoint of the full snake. The assumed absence supplies 19 negative unit clauses. Combine these with the ordinary local path conditions and the joint count cap seven. The extracted input consists of 1046 ordinary clauses and these 19 units, on 826 active variables. Its refutation has 733 derived clauses and 23414 antecedent references.

The ordinary clauses follow from the selected-vertex degrees, the bound of two endpoints, the forbidden square and six-cycles, and the actual missing-corner counts. Each added unit clause is true by the assumed endpoint absence. A generic interpretation of these units and the complete refutation have passed Lean~\cite{endpointarchive}. Hence the hypothetical assignment cannot exist: an endpoint belongs to the displayed set. Translation and the inverse coordinate permutation carry that endpoint back into $G_r$. These maps preserve which two coordinates differ, so its Hamming distance from $x_{r+2}$ is exactly two. The arbitrary-coordinate distance implication has also passed Lean.
\end{proof}

\begin{corollary}[Sharp bound away from the endpoints]\label{cor:endpoint-free-pair}
Under the hypotheses of Theorem~\ref{thm:outer-pair}, if both endpoints have Hamming distance at least three from $x_{r+2}$, then
\[
\alpha_{r+2}+\alpha_{r+6}\ge8.
\]
The constant eight is best possible with this additional hypothesis.
\end{corollary}
\begin{proof}
A sum smaller than eight is at most seven, since the counts are integers. Theorem~\ref{thm:endpoint-demand} would give an endpoint at distance two, contradicting the hypothesis. For sharpness, the 148-edge snake in Appendix~\ref{app:endpoint-witnesses} has the prescribed segment at $r=74$, counts $(\alpha_{76},\alpha_{80})=(5,3)$, and Hamming distance four from $x_{76}$ to each endpoint. The full path, both counts, the segment, and both distances have passed Lean.
\end{proof}

The distance hypothesis concerns the cube metric. Separation by many edges along the path does not imply it. Nor can the hypothesis be weakened to endpoint distance at least two: the 140-edge sharpness example has endpoint distances two and four and still has pair sum seven. This distinction is checked on the complete witness.

'''
marker=r'\section{Retaining empty squares through integer shares}'
replace(marker,new+marker)

# Move the existing weighted endpoint principle next to the new demand set.
a=s.index(r'\subsection{Overlapping endpoint demands}');b=s.index(r'\subsection{A limitation of uniform',a)
accounting=s[a:b];s=s[:a]+s[b:]
accounting=accounting.replace(r'Local geometric arguments often produce sets that must contain an endpoint. Their overlap can be retained in the counting argument.',r'The sets $G_r$ from Theorem~\ref{thm:endpoint-demand} must draw their required endpoints from the same two-element set. The following accounting principle makes this shared restriction explicit. It also applies to other local endpoint demands.')
accounting=accounting.replace(r'\begin{proposition}[Weighted endpoint accounting]',r'\begin{proposition}[Weighted endpoint accounting]\label{prop:endpoint-accounting}')
accounting+=r'''Applying this proposition requires weights for which the bound holds at every cube vertex. Demands from different windows may intersect, so counting every demand as a different endpoint is invalid. The theorem supplies the demand sets; a further overlap estimate is needed for a stronger aggregate bound.

'''
replace(marker,accounting+marker)

# Separate proved geometry from exploratory observations while retaining every record.
observations=[]
starts=['In particular, both counts cannot be at most four in either pattern.',
        'Thus the larger pair sums observed in the 191-edge bank',
        'Independent square enumeration on the sharpness witnesses',
        'The lower bound 28 for $D_3$ is attained',
        'The radius-four local model admits the pairs',
        'Separate local forests have counts',
        'A saved local forest with counts $(3,5,6,8,10,6,3)$']
for prefix in starts:
    a=s.index(prefix);b=s.index('\n\n',a)
    observations.append(s[a:b]);s=s[:a]+s[b+2:]
marker=r'\subsection{Packing numerical window estimates}'
replace(marker,r'\subsection{Local attainments and record-bank observations}\label{app:local-observations}'+'\n'+
        'The following checks concern specified complete snakes or local assignments. The local assignments need not extend to a connected snake. Their results are retained separately from the universal pair and count theorems.\n\n'+'\n\n'.join(observations)+'\n\n'+marker)

# Update the exact finite-model claim to the latest verified graph.
replace(r'Only the four completed cases of the six-centre all-four investigation are used; its unproved remaining cases are admitted.',r'The model also enforces Theorem~\ref{thm:outer-pair} in both orientations. Only the four completed cases of the six-centre all-four investigation are used; its remaining unproved cases are admitted.')
replace(r'on every one of the $4\,561\,226$ retained transitions.',r'on every one of the $4\,551\,730$ retained transitions. The sharp pair restriction removes 9496 transitions from the preceding graph.')
replace(r'Second, the eleven-step cycle printed in Appendix~\ref{app:six-count-cycle} has appended-count sum 42 and $D=c=0$ at every step.',r'Second, the replacement eleven-step cycle printed in Appendix~\ref{app:replacement-cycle} has appended-count sum 42 and $D=c=0$ at every step.')
replace("The cycle shows why the incorporated corrections do not raise this model's limiting mean. It is not a snake construction: overlap of normalized directions and counts does not ensure one globally consistent selected-vertex set. Indeed, stronger radius-four seven-centre solver tests reject all eleven of its windows. Those tests have no replayed contradiction certificates here. They identify additional local exclusions to prove before the graph can be strengthened. The result is specific to this model and supplies no lower limit on what more complete local methods can achieve.",r'''The cycle proves that these incorporated corrections leave this model's limiting mean unchanged. Its overlapping direction and count records do not specify a globally consistent selected-vertex set, so it supplies no snake construction. The endpoint refinement does not exclude it either: at its occurrence of the pattern in Theorem~\ref{thm:outer-pair}, the relevant counts sum to nine, already exceeding the endpoint-free lower bound eight. Other restrictions are therefore needed even after endpoint information is retained. The result is specific to this finite model and places no limit on stronger local or global methods. The preceding eleven-cycle and its numerical rejection tests remain in Appendix~\ref{app:six-count-cycle}, explicitly distinguished from the replacement cycle.''')

# Put the numerical hypothesis before the criteria that refer to it.
a=s.index(r'\section{A numerical conjecture');b=s.index(r'\section{Verification scope',a)
hypothesis=s[a:b];s=s[:a]+s[b:]
at=s.index(r'\section{Construction and the requirements')
s=s[:at]+hypothesis+s[at:]

# Rewrite the verification discussion as a dependency and evidence statement.
a=s.index(r'\section{Verification scope');b=s.index(r'\appendix',a)
verification=r'''\section{Verification scope and remaining problem}\label{sec:verification}
The global conclusion is $191\le a(9)\le236$. The lower bound follows from a finite witness. The upper bound uses a universal reduction: every snake satisfies the square identity and endpoint estimates, every one of its relevant windows avoids the checked catalogue, and every resulting state transition satisfies the finite potential inequality. The summation in Section~\ref{sec:upper-proof} includes the initial six counts, potential range, and both endpoint contributions. No conjecture or restricted-search outcome enters that argument.

The complete 236 theorem has a successful recorded Linux dependency audit in the pinned contributor archive~\cite{radiusfourarchive}. All 732 local refutations and their geometric interpretations are included in the assembled theorem. Its audited axioms are propositional extensionality, classical choice, and quotient soundness. The archived replay summary reports 7190 kernel checks across the reused and new refutations, with approximately 100 kernel-hours in total. An independent local enumeration checks the potential table, and separate Lean checks verify the printed aggregation arithmetic under its stated catalogue and table premises. A fresh independent rebuild of the entire 236 dependency chain remains pending. This is a reproducibility limitation; the archived theorem has discharged its local premises.

The preceding 241 proof has successful source-build and final dependency-audit receipts on two platforms. The 238 proof has a successful final Linux audit against an incremental build. Its 175 refutations contain about 4.6 million derived clauses and 270 million antecedent references, replayed through 2803 kernel checks. These are recorded verification statistics, not substitutes for the soundness argument. Detailed earlier geometric classifications are retained in Appendix~\ref{app:geometry}; the account of the three-count classification is explicitly an outline and does not reproduce every branch.

The pair theorems, empty-square accounting, and joint-count deductions have the verification scope stated with their proofs. The outer-transition inequality and its counterexamples have 16 dependency audits; the endpoint-demand refinement and its sharpness example have another 16. Their arbitrary-snake deductions, coordinate transport, and complete witness checks use only the standard axioms listed above. The sharpness witnesses show that stronger constants require additional hypotheses. They do not establish any candidate for the longest snake.

The finite graph is verified separately by an attaining cycle and an integer potential checked on every retained edge. This establishes its exact mean $42/11$. A complete Lean proof connecting that generated graph to arbitrary snakes has not been assembled. Local forests establish only local feasibility, numerical infeasibility without a replayed proof retains that status, and an unresolved search establishes neither existence nor impossibility. The archived restricted construction searches cover their stated fixed regions and templates only.

The exact optimum remains open. No construction above 191 edges and no universal exclusion of length 192 has been obtained here. A stronger upper bound requires a charge estimate covering every admissible sequence, with endpoint and overlap losses included. The endpoint demand sets provide a new constraint on equality cases, while the surviving cycle shows that this constraint alone is insufficient. On the construction side, every valid 192-edge snake would already improve the record considered in this paper. The conjecture $a(9)=196$ requires both a 196-edge construction and a universal exclusion of 197 edges.

'''
s=s[:a]+verification+s[b:]

# Print the replacement cycle; preserve the previous cycle as historical evidence.
g=json.loads((ROOT/'milestones/44-critical-window-generalization/data/analysis.json').read_text())
rows='\n'.join(str(i)+' & $('+','.join(map(str,r['directions']))+')$ & $('+','.join(map(str,r['counts']))+r')$\\' for i,r in enumerate(g['cycle']))
newcycle=r'''\subsection{The replacement cycle after the sharp pair restriction}\label{app:replacement-cycle}
The following cycle belongs to the graph with the outer-transition pair inequality imposed in both orientations. Directions and count symbols specify the states as described in Section~\ref{sec:common-budget}.
\begin{center}
\begin{tabular}{rll}
\toprule
Phase & Directions & Seven internal count symbols\\\midrule
'''+rows+r'''
\bottomrule
\end{tabular}
\end{center}
Every demand and share indicator is zero. The appended counts sum to 42. Thus the normalized mean is $42/11$, matching the all-edge potential on the 4551730 retained transitions. The source graph had 4561226 transitions; the pair inequality removes 9496. The unchanged potential has range 8064. Both the cycle and every retained edge were checked by exact integer arithmetic~\cite{outerpairarchive}.

At phase four, the direction word is the normalized pattern of Theorem~\ref{thm:outer-pair}; its second and sixth count symbols are four and five. Their sum nine satisfies the endpoint-free bound eight. This cycle therefore remains a numerical obstruction even if that stronger local bound is added at every such occurrence. No claim of realization by a complete snake is made.

'''
replace(r'\subsection{The exact six-count model certificate}',newcycle+r'\subsection{The preceding six-count cycle}')
replace(r'The following eleven transitions form a closed cycle in the enlarged graph of Section~\ref{sec:common-budget}.',r'The following eleven transitions form a closed cycle in the preceding graph, before Theorem~\ref{thm:outer-pair} was imposed. Phase two has pair sum six and is excluded by that theorem. The table is retained to identify precisely which obstruction the new proof removes.')
replace(r'Each row was also tested with its seven displayed counts as upper caps in the stronger radius-four acyclic window model. All eleven tests returned infeasibility. These numerical outcomes have no replayed refutations in this record, so they are not added to the proved exclusion family. They provide candidates for the next certificate work.',r'Each row was also tested with its seven displayed counts as upper caps in the stronger radius-four acyclic window model. All eleven tests returned infeasibility. Theorem~\ref{thm:outer-pair} now supplies a checked general exclusion covering phase two. The other ten numerical results have no individual replayed refutations in this record. Their status is unchanged by the proof for phase two.')
replace(r'The first subsection records the exact finite-model result used in Section~\ref{sec:common-budget}. The remaining subsections retain earlier diagnostics in their order of development.',r'The first subsection records the current exact finite-model result used in Section~\ref{sec:common-budget}; the second preserves its preceding cycle. The remaining subsections retain earlier diagnostics in their order of development.')

# Add all new complete witnesses in directly reproducible transition notation.
witnesses=[]
for relative,title in [('44-critical-window-generalization/data/witness-sharp.json','The sharp bound seven'),('44-critical-window-generalization/data/witness-short.json','The shorter-context counterexample'),('45-pair-endpoint-demand/data/witness-endpoint-sharp.json','The sharp endpoint-free bound eight')]:
    r=json.loads((ROOT/'milestones'/relative).read_text());vs=r['vertex_sequence']
    ds=[(a^b).bit_length()-1 for a,b in zip(vs,vs[1:])]
    groups=[''.join(map(str,ds[i:i+10])) for i in range(0,len(ds),10)]
    lines=[' '.join(groups[i:i+5]) for i in range(0,len(groups),5)]
    witnesses.append(dict(title=title,edges=len(ds),start_vertex=vs[0],window_start=r['start'],pair_counts=r['pair_counts'],vertex_sequence=vs,transitions=ds))
    r['text']=r'\paragraph{'+title+r'.} Start at vertex '+str(vs[0])+', giving a '+str(len(ds))+'-edge snake. The specified segment starts at index '+str(r['start'])+'.\n'+r'\begin{quote}\small\ttfamily'+'\n'+('\\\\\n'.join(lines))+'\n'+r'\end{quote}'+'\n'
    witnesses[-1]['text']=r['text']
listing=r'''\subsection{Sharp pair and endpoint-distance witnesses}\label{app:endpoint-witnesses}
These three complete snakes distinguish the full eight-transition hypothesis, its shorter subsegment, and the additional endpoint-distance assumption. Every vertex pair, displayed segment, and pair count has been checked in Lean. For the 140-edge example the counted centre has endpoint distances two and four; for the 148-edge example both distances are four.

'''+ '\n'.join(r['text'] for r in witnesses)+'\n'
replace(r'\subsection{A radius-three linear forest}',listing+r'\subsection{A radius-three linear forest}')

refs=r'''\bibitem{outerpairarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Sharp outer-transition pair inequality, complete counterexamples, and replacement finite-model cycle}. Archived research record, 24 October 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/c05997bad7eaf5f6f34c547df794cee4a946f893/milestones/44-critical-window-generalization}.

\bibitem{endpointarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Endpoint demand and the sharp endpoint-free pair bound}. Archived research record, 25 October 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/c0a672d7d314317bf69332fc7029e00853e16b04/milestones/45-pair-endpoint-demand}.

'''
replace(r'\end{thebibliography}',refs+r'\end{thebibliography}')
assert s.split(r'\begin{abstract}')[0]==old.split(r'\begin{abstract}')[0]
(HERE/'data').mkdir(parents=True,exist_ok=True)
(HERE/'data/new-witnesses.json').write_text(json.dumps([{k:v for k,v in r.items() if k!='text'} for r in witnesses],indent=2)+'\n')
# Update the existing open source in place, then synchronize the repository source.
editor.write_text(s,encoding='utf-8',newline='\n');paper.write_bytes(editor.read_bytes())
print('Revised existing source:',len(s.splitlines()),'lines;',hashlib.sha256(paper.read_bytes()).hexdigest())
