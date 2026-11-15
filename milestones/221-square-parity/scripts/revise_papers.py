from pathlib import Path

H=Path(__file__).resolve().parents[1]
R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')

def replace_once(s,old,new):
    assert s.count(old)==1,old[:100]
    return s.replace(old,new)

p=D/'snake9_research.tex'
s=p.read_text(encoding='utf-8')
assert s==(H/'data/before-snake9_research.tex').read_text(encoding='utf-8')
s=replace_once(s,'Research state after round 220,','Research state after round 221,')
s=replace_once(s,r'''Exact fractional certificates show that the fixed-parent degree
formulation, even with every cycle occupancy and subset forest inequality,
cannot exclude the 94-vertex compatible-partner target. The subset
inequalities nevertheless give exact certificates excluding a 97-edge
partner for this representative. Explicit failures of Boolean product
consistency identify a further class of valid inequalities.''',r'''Exact certificates exclude a 95-edge compatible partner at either
endpoint of the saved 98-edge parent. Its one-crossing construction
therefore has at most 193 edges. The 93-edge partner needed for 192
remains unresolved. Exact fractional points satisfy the degree and
linear product constraints together with every cycle occupancy,
subset forest and disagreement-cycle parity inequality at total weight
94. Fixing an actual first step excludes three of fourteen branches;
the other eleven remain open.''')
s=replace_once(s,r'\subsection{The next missing constraint: consistency of edge products}',r'\subsection{Consistency of edge products}')
s=replace_once(s,'The new root-0 fractional point assigns the following disagreement values','The round-220 root-0 fractional point assigns the following disagreement values')
s=replace_once(s,r'''The two square parity forms have a separate Boolean Lean check;
the general cycle assertion has the elementary proof above.
No strengthened linear program containing these parity rows has yet
been solved in this round, and no improved bound is inferred from them.''',r'''The two square parity forms have a separate Boolean Lean check.
The subsequent computation below adds these constraints and longer
cycle inequalities; it also checks the general parity argument in Lean.''')
new=r'''
\subsection{Parity-strengthened bounds and first-step restrictions}
\label{sec:parity221}
Every closed Boolean walk changes value an even number of times, as
induction on the walk proves. If $F$ is an odd marked edge set, the
disagreement pattern must differ from its indicator on at least one edge.
The left side of~\eqref{eq:cut-parity220} equals $|F|$ minus the number
of mismatches, proving the inequality. Lean checks this argument for
an arbitrary closed Boolean walk, with closure explicit and even parity
derived from its successive vertex values.

The allowed graphs at roots 0 and 78 have 156 and 154 coordinate squares.
All eight odd-subset inequalities on each square are added. Their exact
upper certificates are 96.000722 and 95.779317. Rational points still
violate longer cycle inequalities. Adding 27 such rows at root 0 and
eight at root 78, together with one further subset row at root 78, gives
\[
\begin{array}{c|c|c}
\text{Root}&\text{Exact feasible total weight}&\text{Exact upper bound}\\\hline
0&\displaystyle\frac{2507137819890885477}{26128236866583647}&95.955197\\[6pt]
78&\displaystyle\frac{388107824092577}{4052758842992}&95.763979.
\end{array}
\]
The upper bounds follow from integer weighted rows and residual bounds
on variables in $[0,1]$, as in Section~\ref{sec:linear219}. Every new row
and the exact arithmetic have independent audits. Numerical optimality
of the linear programs is unnecessary for the upper-bound deduction.

\begin{proposition}[Restriction for the saved parent]\label{prop:parent193}
For the specified 98-edge parent, any compatible path beginning at either
endpoint has at most 94 edges. Its one-crossing join has at most 193 edges.
\end{proposition}
\begin{proof}
A 95-edge partner has 96 vertices and satisfies the odd-edge model.
Both upper certificates are strictly below 96, so such a partner is
excluded. Any longer partner contains a compatible 95-edge prefix.
Thus its length is at most 94, and the join has length at most
$98+94+1=193$. The argument uses this parent and these two roots only.
\end{proof}

\paragraph{A complete-family fractional obstruction.}
The two rational points in the table satisfy every occupancy-cycle
inequality and every subset forest inequality. This follows from 337
edge-deleted potential systems and 158 feasible flows per root, by the
arguments of Sections~\ref{sec:linear219} and~\ref{sec:forest220}.
They also satisfy every disagreement-cycle parity inequality, including
those absent from the finite model. To certify this, replace each vertex
by two copies. Each original edge has layer-preserving cost $d_{uv}$
and layer-switching cost $1-d_{uv}$, in both directions. For each original
vertex $v$, a saved rational potential is zero at its first copy and
at least one at its second; every directed arc satisfies
$p(b)-p(a)\le c_{ab}$. A cycle marked on an odd set $F$ lifts to a walk
between these two copies. Summing the arc inequalities yields
\[
\sum_{e\in F}(1-d_e)+\sum_{e\in E(C)\setminus F}d_e\ge1,
\]
which rearranges to~\eqref{eq:cut-parity220}. All 158 potential systems
are checked exactly at each root. The argument needs feasible potentials,
without a claim of shortest-path optimality.

Mixing either point of weight $q$ with the corresponding one-edge path,
with weight $92/(q-2)$ on the larger point, gives weight exactly 94.
Every asserted family is linear and persists under this mixture.
Independent exact audits therefore establish that the continuous model
with all three complete families still admits the target weight.
These fractional assignments provide no induced path. The generic Lean
implications remain separate from the concrete numerical assembly.

\paragraph{Requiring an actual first step.}
The root must choose exactly one of its seven allowed neighbours.
Adding $x_w=1$ for each possible first neighbour $w$ gives the exact
cardinality upper bounds below. The root degree equation then sets
the other six neighbour variables to zero.
\[
\begin{array}{c|r|r@{\qquad}c|r|r}
\text{Root}&w&\text{Upper bound}&\text{Root}&w&\text{Upper bound}\\\hline
0&2&94.488969&78&14&93.517327\\
0&4&94.613095&78&74&93.927558\\
0&8&94.558772&78&76&94.463971\\
0&16&92.569610&78&79&94.406607\\
0&32&95.018845&78&94&94.229213\\
0&64&95.680069&78&110&94.892792\\
0&128&94.188343&78&206&94.951566
\end{array}
\]
Every 93-edge partner occurs in one of these branches. Since it has
94 vertices, the branches $0\to16$, $78\to14$ and $78\to74$ are excluded.
The other eleven remain unresolved: their upper bounds alone do not
prove feasibility. Extending these remaining prefixes is a concrete
next step. All certificates and scope records are retained in
milestone 221~\cite{research221}.

'''
s=replace_once(s,r'\section{Verification scope and remaining problem}',new+r'\section{Verification scope and remaining problem}')
s=replace_once(s,r'''For the fixed 98-edge parent, the exact subset-weight certificates now
exclude a 97-edge partner at either endpoint. The 93-edge targets remain
open. Exact fractional assignments satisfy every cycle occupancy and
subset forest inequality at total weight 94, but fail Boolean product
consistency on explicit squares. The corresponding generic Lean
results, exact finite audits and unresolved numerical assembly are
distinguished in Sections~\ref{sec:linear219}--\ref{sec:product220}.''',r'''For the fixed 98-edge parent, exact parity-strengthened certificates
exclude a 95-edge partner at either endpoint, giving a one-crossing
ceiling of 193. The 93-edge targets remain open. Exact fractional
assignments satisfy every occupancy-cycle, subset-forest and
disagreement-cycle parity inequality at total weight 94. Requiring an
actual first step excludes three of fourteen branches. The corresponding
generic Lean results, exact finite audits and unresolved numerical
assembly are distinguished in
Sections~\ref{sec:linear219}--\ref{sec:parity221}.''')
bib=r'''\bibitem{research221}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Cycle parity, exact partner bounds
and first-step restrictions}. Research milestone 221, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/221-square-parity}.

'''
s=replace_once(s,r'\bibitem{barahona1986}',bib+r'\bibitem{barahona1986}')
p.write_text(s,encoding='utf-8',newline='\n')
(R/'paper'/p.name).write_bytes(p.read_bytes())

p=D/'snake9_frontier_explanation.tex'
s=p.read_text(encoding='utf-8')
assert s==(H/'data/before-snake9_frontier_explanation.tex').read_text(encoding='utf-8')
s=s.replace('round 220','round 221')
start=s.index('Relax the Boolean variables to $[0,1]$')
end=s.index(r'\section{Remaining questions}',start)
s=s[:start]+r'''Relax the Boolean variables to $[0,1]$ and retain the linear product
inequalities and degree equations. Boolean product consistency gives
another necessary family. Put $\delta_{ab}=x_a+x_b-2y_{ab}$.
For Boolean selections this is one exactly when the endpoint selections
differ, so a closed cycle has an even number of changes. For any odd
subset $F$ of its edges, at least one edge must disagree with the marked
pattern $F$. Hence
\[
\sum_{e\in F}\delta_e-\sum_{e\in E(C)\setminus F}\delta_e\le|F|-1.
\]
Lean checks this argument for arbitrary closed Boolean walks. The
inequalities are classical~\cite{barahona1986}.

Adding square and longer parity inequalities to the subset model gives
exact cardinality upper certificates 95.955197 at root 0 and 95.763979
at root 78. Both are below 96, excluding a 95-edge partner. Every longer
partner has such a prefix; therefore arbitrary compatible partners
at these two roots have at most 94 edges. This particular parent's
one-crossing construction consequently has at most $98+94+1=193$ edges.
The 93-edge partner needed for 192 remains possible.

The exact fractional feasible cardinalities are
\[
q_0=\frac{2507137819890885477}{26128236866583647},\qquad
q_{78}=\frac{388107824092577}{4052758842992}.
\]
Both exceed 94 and satisfy three complete families, beyond the finite
rows explicitly added to the model. For occupancy cycles, put $w_u=1-x_u$.
For each deleted edge $ab$, a potential has $p_a=0$,
$|p_u-p_v|\le w_u+w_v$ on other edges and $p_b+w_a+w_b\ge2$.
Summing around any cycle gives $\sum_{u\in C}w_u\ge1$.
For subset inequalities, 158 feasible flows per root send at least
$2x_v$ from $v$ to an added sink. Conservation bounds this supply by
every separating cut, whose capacity is exactly $B+E$ above.

For parity cycles, make two copies of every allowed vertex. An edge
preserving the copy label costs $\delta_{ab}$, and one switching it
costs $1-\delta_{ab}$. For each vertex, a saved potential increases
by at least one between its two copies, with every arc satisfying
$p(b)-p(a)\le c_{ab}$. Following a cycle while switching on its odd
marked subset ends at the opposite copy. Telescoping gives total cost
at least one, which is the displayed parity inequality.
All these rational potential and flow certificates pass independent
exact arithmetic audits. Their generic arguments and the concrete
numerical arrays retain separate verification records.

Mix either point with the corresponding one-edge path using weight
$92/(q_t-2)$ on the larger point. The mixture has weight exactly 94,
and linearity preserves all three complete families. Thus this full
continuous relaxation cannot exclude the target. No path is constructed
by these fractional assignments~\cite{research220,research221}.

An actual path also chooses one definite first neighbour. Each root
has seven choices. Exact conditional upper certificates below 94 exclude
$0\to16$, $78\to14$ and $78\to74$ from any 93-edge partner.
The remaining eleven choices are unresolved. Extending their prefixes
is the next finite search; an upper bound above 94 does not establish
the existence of a branch completion.

'''+s[end:]
s=replace_once(s,r'\bibitem{barahona1986}',bib+r'\bibitem{barahona1986}')
p.write_text(s,encoding='utf-8',newline='\n')
(R/'paper'/p.name).write_bytes(p.read_bytes())
print('UPDATED_EXISTING_PAPERS_AND_EXACT_MIRRORS_221')
