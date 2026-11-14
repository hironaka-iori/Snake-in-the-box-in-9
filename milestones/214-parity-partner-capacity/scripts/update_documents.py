"""Update the existing editor sources and their exact repository mirrors."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
summary=json.loads((H/'data/search-summary.json').read_bytes())
assert summary['status']=='OPEN' and summary['new_jobs']==120
assert json.loads((H/'data/PathTight214-audit.json').read_bytes())['status']=='PASS'
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    target=H/'data'/('before-'+name);assert not target.exists()
    target.write_bytes((D/name).read_bytes())
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
front=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=main.replace('Research state after round 213, 15 November 2026','Research state after round 214, 15 November 2026',1)
front=front.replace('Research state after round 213','Research state after round 214',1)
main=main.replace('construction lower bound are unchanged in this round.','construction lower bound were unchanged in round 213.',1)
new=r'''
\subsection{Parity alphabets and tight partner subsets}
\label{sec:tight214}
The next question is whether competition for partners gives deductions
even when every outside interval has an individually supported word.
The answer is affirmative at a tight subset. It supplies a stronger
necessary restriction, without asserting that a partner matching can
be assigned consistent word labels.

First, the parity alphabet follows from the normalized reconstructed
path. Between group $g$ and group $g+1$, the retained base is unchanged
and one free coordinate changes. Hence the parity of the free word
flips. If the first free word is zero, induction gives
\[
\operatorname{wt}(u_g)\equiv g\pmod 2.
\]
Each parity class of $Q_6$ contains 32 words: toggling a fixed coordinate
pairs the even and odd classes. The checked literal boundary witnesses
establish every group transition for the saved $(0,6)$ source. The
six-bit parity masks and their cardinalities are also checked.
The raw integer representation is required to lie below 64; six-bit
decoding alone would permit larger integers with identical decoded bits.

For one parity, let $C$ and $O$ be the chosen and outside interval
families, with distinct assigned words within each family. Put
$s=32-|C|$. For $J\subseteq O$, let $N(J)\subseteq C$ contain every
listed partner of a member of $J$ whose current domain intersects that
member's domain. The earlier capacity argument gives
$|J|\le |N(J)|+s$.

\begin{proposition}[Tight partner capacity]\label{prop:tight214}
If $|J|=|N(J)|+s$, every interval in $O\setminus J$ shares its word
with a chosen interval in $C\setminus N(J)$. Consequently its domain
may be restricted to the union of its listed partners' domains outside
$N(J)$, preserving every complete assignment that satisfies the path
and current-domain conditions.
\end{proposition}
\begin{proof}
Let $E$ be the outside intervals whose assigned words do not occur in
$C$. The chosen words and these distinct additional words fit in 32
positions, so $|E|\le s$. Every word assigned to $J$ occurs either
among the values on $N(J)$ or among the values on $E$. Therefore
\[
|J|\le |N(J)|+|E|\le |N(J)|+s=|J|.
\]
All inequalities are equalities. Thus the words on $J$ exhaust both
the partner values on $N(J)$ and all exceptional values. An interval
of $O\setminus J$ has a different word from every interval of $J$.
Its word is consequently nonexceptional and cannot equal a value on
$N(J)$, proving the assertion. Its actual partner's word belongs to
that partner's current domain, which proves preservation under the
stated restriction.
\end{proof}

The rule can strengthen individual support even when no interval is
forced to be exceptional. For example, use four words $\{0,1,2,3\}$
and three chosen values fixed to $0,1,2$. Suppose outside intervals
$x,y$ both have domain $\{0,3\}$ and can share only with the chosen
value $0$. They consume that word and the one spare word. An outside
interval $z$ with domain $\{0,1,2,3\}$ must therefore use $1$ or $2$.
Each of $x,y,z$ initially has partner support, so the earlier rule
counting individually unsupported intervals makes no such deduction.

Lean checks Proposition~\ref{prop:tight214}, preservation of the
same complete assignment, and the composition from the normalized
reconstructed path for both parity families. Current-domain fitting,
candidate coverage and support containment remain explicit.
A matching with $s$ additional partner slots
is used only to discover deficient or tight subsets; every native
deduction recomputes and checks the required neighbor cardinality.
The native search and its saved traversal retain their separate
verification status~\cite{research214}.

The separate continuation preserves the eleven saved regions before
applying the stronger engine. Its 120 new jobs examine 749,506 nodes:
105 subtrees are exhausted and 15 return unfinished regions. The added
rule records 3,054 value removals and 120 contradiction returns.
These count repeated operations across branches. The case remains
open, with thirteen saved regions and 1,801,017 cumulative nodes.
No controlled comparison establishes a speed improvement, and no new
snake or complete six-coordinate exclusion follows.

'''
anchor='\\section{Verification scope and remaining problem}\\label{sec:verification}'
assert main.count(anchor)==1
main=main.replace(anchor,new+anchor,1)
entry=r'''
\bibitem{research214}
Snake-in-the-box project. \emph{Parity alphabets and tight partner
capacity: checked deductions and native continuation}. Research
milestone 214, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/214-parity-partner-capacity}.

'''
assert main.count('\\end{thebibliography}')==1
main=main.replace('\\end{thebibliography}',entry+'\\end{thebibliography}',1)
short=r'''
\paragraph{The next restriction: a tight partner subset.}
Starting the free word at zero fixes its parity: each group change
flips one free coordinate, so group $g$ uses parity $g\bmod2$.
The saved group boundaries and the two 32-word alphabets are now
checked in Lean, with six-bit integer range stated explicitly.

For one parity let $s=32-|C|$. If a subset $J$ of outside intervals
has only $N(J)$ possible chosen partners, then
$|J|\le |N(J)|+s$. At equality, the words used by $J$ exhaust both
those partner values and every unused-word allowance. All other
outside intervals have distinct words, so they must share with
partners outside $N(J)$. Their domains can be restricted accordingly.
Lean checks the counting argument and assignment preservation.
This can strengthen individual support when several intervals compete
for a small partner set. A matching discovers candidate subsets;
matching success alone does not establish a realizable snake.
The new continuation examines 749,506 additional nodes and records
3,054 value removals by this rule. Thirteen regions remain unfinished;
the known lower bound and the number of unresolved coordinate choices
are unchanged.

'''
anchor='\\section{What would resolve the question}'
assert front.count(anchor)==1
front=front.replace(anchor,short+anchor,1).replace('milestones through round 213','milestones through round 214',1)
front=front.replace('separate. No construction search state changes in this round.','separate at the end of round 213.',1)
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
    (D/name).write_text(text,encoding='utf-8',newline='\n')
    (R/'paper'/name).write_bytes((D/name).read_bytes())
print('UPDATED_EXISTING_DOCUMENTS')
