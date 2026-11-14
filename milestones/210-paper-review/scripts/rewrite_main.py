"""Revise the preserved manuscript, then mirror the editor source exactly."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
EDITOR = Path(r'D:\Codex\2026-10-13\new-chat\outputs\snake9_research.tex')
source = (HERE / 'data/research-before.tex').read_text(encoding='utf-8')
lines = source.splitlines(keepends=True)
edits = []
def replace_lines(first, last, text):
    edits.append((first, last, text.rstrip() + '\n'))

replace_lines(32, 33, r'''\title{Bounds and Constructions for the\\
Nine-Dimensional Snake-in-the-Box Problem}''')
replace_lines(39, 99, r'''Let $a(9)$ denote the maximum edge length of an induced path in the
nine-dimensional binary hypercube. An explicit checked construction and
a completed archived contributor theorem give $191\le a(9)\le235$.
The saved upper-bound audit is successful; its complete independent
rebuild remains pending.

For a snake of length $m$, singleton-square count $T$ and empty-square
count $s_0$, the exact census is $T+2s_0+35(m+1)=9214$.
Local count restrictions strengthen the archived argument to
$39m+2s_0\le9192$. Thus fourteen empty squares would suffice to exclude
length 235. Integer shares retain the empty-square contribution in
stronger conditional comparisons. Four unresolved local share floors,
$(15,14,14,14)$, together with specified graph and certificate premises,
would give $a(9)\le234$. A separate contributor comparison targets 233.

The construction analysis derives restrictions on joining paths in
opposite coordinate faces and gives criteria for changing an entire
snake while preserving all selected adjacencies and nonadjacencies.
For the saved 98-edge parent in dimension eight, exhaustive native
searches over four and five free coordinate histories find no different
cube-isometry class at the same length and fixed index matching.
At least six histories must therefore change within that comparison.
A capacity inequality for a square of fixed coordinates forces nine
shared free words in one remaining six-coordinate case. Its geometric
core, counting implications and literal source counts have separate
Lean checks; the complete finite search certificates and geometric
assembly retain their stated limitations.

The paper separates written proofs, checked implications, native
enumerations and unresolved premises. No construction above 191 or
improved unconditional numerical bound is obtained. The value 196
remains a conjecture requiring both a construction and an upper bound.''')
replace_lines(144,145,r'''The upper bound is the completed contributor theorem at the cited archival
revision, with a successful saved compilation and axiom audit. A complete
independent rebuild of its dependency closure remains pending.''')
replace_lines(149,162,r'''The argument has two parts. The first develops the square census,
local count restrictions and empty-square shares, then states the precise
remaining conditions for bounds 234 and 233. The seven-count boundary
allows the current retained comparison to use nonnegative loss alone.
The second examines numerical conjectures, constructions across
dimensions, transformations of whole snakes and restrictions obtained
by fixing coordinate histories. The final section records verification
scope and the unresolved extremal problem. Historical comparison models,
restricted construction experiments and explicit witnesses are retained
in the appendices. Every historical comparison keeps its original graph,
weights and boundary; later improvements do not silently change its premises.''')
replace_lines(781,785,r'''The preceding weaker geometric argument was initially checked only through
its local pair-and-triple implications and incidence arithmetic. The stronger
result below completes the actual-cube and path interpretation and gives
$e(q)\ge8$, hence also the loss-59 consequence above. The degree-only
bound four is sharp:''')
replace_lines(2726,2732,r'''For $m\ge9$, its total weight $W=\sum_{r=0}^{m-9}w_r$ satisfies
\[
W+2880\le5G_{12},\qquad W+4200m+5L\le1098600,
\]
where $L=\sum_qr_{12}(q)\ge0$ is the total loss.
The same statements hold for the conditional floor choice under the five
local share bounds just stated. Neither total-weight assertion requires
the reference-catalogue premise. The earlier boundary-21 totals follow
as weaker consequences.''')
replace_lines(2751,2759,r'''The omitted singleton positions are $0,1,\ldots,7,m$. The endpoint
bounds and the seven-count floor give
\[
\sum_{r=0}^{m-9}\alpha_{r+8}+24\le T.
\]
Each share occurs at most five times. Therefore
$W+2880\le120T+5\Sigma=5G_{12}$. Substituting the exact identity
$5G_{12}+4200(m+1)+5L=1105680$ gives the claimed total.
These deductions use the checked boundary-24 implication proved above;
the local-share premises remain exactly those of the chosen floor profile.''')
replace_lines(3980,3987,r'''\paragraph{Current retained graph.}
The sufficient profile is $(15,14,14,14)$ on
$012034,012301,012340,012345$. It applies to the specified retained
graph with 4661572 transitions. Its proof requires completion of the local
certificates and their actual-snake interpretation, including the
extension condition used for $012301$ when $m\ge7$. It also retains the
specified six-count condition on $0123104$, reference and context
exclusions, graph coverage and the complete finite-edge certificate.
These premises are separate from the accepted-key package below.''')
replace_lines(4003,4005,r'''\paragraph{Earlier accepted-key route.}
The separate 4947008-key argument has checked graph coverage and weight
interpretation under its own assumptions. Its archived sufficient
profile and remaining certificate obligations are as follows.''')
replace_lines(4033,4046,r'''Proposition~\ref{prop:least-floors} concerns the least sufficient integer
floors within its fixed historical box and boundary. Likewise,
Proposition~\ref{prop:two-cycle-share16-obstruction} concerns its original
weights: when the $012301$ and $012340$ floors are at most 16 and the
eleven-cycle remains unchanged, its comparison is at least
$235+95/2348$, with necessary relation $325F+159G>9074$.
The proved $012032$ share-16 floor adds 57 to that cycle and removes
the unchanged-weight hypothesis. Proposition~\ref{prop:range156-optimum}
records the subsequent fixed-profile comparison; the current
boundary-24 profile is treated in Section~\ref{sec:floor14-loss}.
These are distinct finite comparisons. Completing one package does not
establish another package's actual-snake interpretation.''')
replace_lines(5887,5887,lines[5886].replace('A check of all $8^3$ clamped triples shows that',r'''The enumeration uses values zero through seven with positivity guards;
zero is discarded, leaving the stated 49 positive pair states.
A check of all $8^3$ clamped triples shows that'''))
replace_lines(3465,3466,r'''Together with the maintained upper bound 235, it suffices to exclude
length 235. Its odd parity supplies this particular graph premise;
the other premises still require proof.''')
replace_lines(6867,6869,r'''In round 191, the cases $r=6$ and $r=7$ were reported infeasible in
13.203 and 30.344 seconds, respectively, before any additional cycle
exclusion. The resulting restriction for this particular 95-edge path was''')
replace_lines(7206,7209,r'''\paragraph{The 44-edge single-replacement cutoff.}
All single length-preserving replacements of blocks of at most 44
edges, followed immediately by one endpoint addition, were computationally
excluded in round 194 for every saved 191-edge snake. The search''')
replace_lines(7542,7546,r'''At that cutoff, one possible subdivision retained the contact $(4,38)$
as a path edge and removed at least one ordinary neighbour of each
endpoint; another omitted a contact endpoint and repaired the break.
Keeping the original two seed endpoints requires an odd number of
matching steps. Maintaining one ordered path excludes disconnected cycles.''')
replace_lines(8625,8625,r'''Lean checks complete coverage of all 254 explicit finite models in 625
data, elimination and cover modules. The result quantifies over assignments
to the stored domains and compatibility tables.''')
replace_lines(8916,8920,r'''At the round-209 cutoff, the added deductions are active in a separately
reviewed native search. Retained pairs $(0,4)$, $(3,4)$ and $(0,5)$ remain
open. The other 24 unresolved pairs retain only their initial limited
searches. The exhausted pair $(1,4)$ remains the sole six-coordinate
exclusion. No new parent or global $Q_9$ bound follows.''')
replace_lines(7995,8007,''.join(lines[7994:8006])+r'''gives a longer $Q_9$ snake or a new global numerical bound~\cite{research201}.''')
replace_lines(8429,8431,r'''The following section records partial certification of this comparison.
Further construction requires different parents or changes outside
the covered slice-isometry family.''')
replace_lines(8899,8905,r'''The same saturation restricts every unfinished branch. Each even word
must remain available to at least one of the 32 selected interval
variables. If exactly one of their domains contains that word, that
variable is forced to take it. A remaining singleton variable may use
only words still available to its opposite-corner partners. Each
deduction preserves every completion of the original model.''')

for first,last,new in sorted(edits, reverse=True):
    lines[first-1:last] = [new]
s = ''.join(lines)
replacements = {
    r'Appendix~\ref{sec:optimality}':r'Section~\ref{sec:optimality}',
    '[Potential criterion for excluding 235]':'[Boundary-21 potential criterion for excluding 235]',
    '[Potential comparison retaining the loss]':'[Boundary-21 comparison retaining the loss]',
    'six directions of memory are necessary and sufficient for this value':'within this tested family and rule catalogue, six directions of memory first attain this value',
    'A useful first restricted target is':'The next restricted target was',
    'The next construction search can impose':'The subsequent construction search imposed',
    'The next attempt uses':'The round-196 continuation used',
    'Round194':'Round 194','shorter189-edge':'shorter 189-edge',
    'nonadjacent42-edge':'nonadjacent 42-edge','involutions:20':'involutions: 20',
    'original96-vertex':'original 96-vertex','quotient,16':'quotient, 16',
    'record195':'record 195','November2026':'November 2026',
    'actual-snake share theorems remain unfinished.':'actual-snake share theorems were unfinished at this archived cutoff.',
    'The complete contradiction and its application to arbitrary snakes remain pending.':'The complete contradiction and its application to arbitrary snakes were pending at this archived cutoff.',
}
for old,new in replacements.items():
    s = s.replace(old,new)

# Local share symbols in these historical comparisons are distinct from total loss.
a=s.index(r'\subsection{Complete models before the eleven-transition refinements}')
b=s.index(r'\subsection{Restricted families and replacement cycles}',a)
chunk=s[a:b].replace('$120b_{\\mathrm{new}}+L$, where $L$', '$120b_{\\mathrm{new}}+H$, where $H$')
s=s[:a]+chunk+s[b:]
a=s.index(r'\section{The earlier five-window model and its zero-credit obstruction}')
b=s.index(r'\section{',a+10)
chunk=re.sub(r'\bL(?=[^A-Za-z0-9]|$)','H',s[a:b])
s=s[:a]+chunk+s[b:]

s=s.replace(r'$120b_{\mathrm{new}}+L$, without division by 120.',
            r'$120b_{\mathrm{new}}+H$, where $H$ is the local share bound, without division by 120.')

# Bring all dimensional and whole-snake deductions into the main argument.
a=s.index(r'\section{A numerical conjecture and its limitations}\label{sec:hypothesis}')
b=s.index(r'\section{Construction experiments and their scope}\label{app:experiments}',a)
construction=s[a:b]
s=s[:a]+s[b:]
anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}'
s=s.replace(anchor, r'\part{Constructions and whole-snake restrictions}'+'\n'+construction+anchor,1)
anchor=r'\section{The exact square census}'
if anchor in s:
    s=s.replace(anchor,r'\part{Square counts and upper-bound deductions}'+'\n'+anchor,1)
else:
    # The first counting section follows the stated lower bound.
    a=s.index(r'\end{proof}',s.index(r'\begin{theorem}[Verified lower bound]'))+len(r'\end{proof}')
    s=s[:a]+'\n\n'+r'\part{Square counts and upper-bound deductions}'+s[a:]

anchor=r'\appendix'
status=r'''\paragraph{Construction and history verification.}
The two-parent identities and whole-snake preservation criteria have the
written proofs given above. Their checked arithmetic and finite geometric
components retain the explicit assembly limits stated in each subsection.
For the saved 98-edge parent, Lean checks literal coverage of 254 stored
slice-isometry models; the connections from their tables to arbitrary
geometric choices remain pending. The exhaustive four- and five-history
exclusions are native calculations, with complete finite exclusion
certificates still pending. At the round-209 cutoff, only retained pair
$(1,4)$ among the 28 six-history cases is exhausted. The other 27 remain
unresolved. The capacity inequality and source counts add sound necessary
conditions, without producing a different parent or a longer $Q_9$ snake.
The whole-paper review in round 210 changes presentation and proof-status
accounting; it makes no new search or numerical-bound claim.

'''
s=s.replace(anchor,status+anchor,1)
anchor=r'\bibitem{research202}'
entry=r'''\bibitem{research201}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Fundamental restrictions on
two-parent constructions}. Research record 201, November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/201-crossing-deletion}.

'''
if anchor not in s:
    raise RuntimeError('Missing bibliography insertion anchor')
s=s.replace(anchor,entry+anchor,1)
EDITOR.write_text(s,encoding='utf-8',newline='\n')
(ROOT/'paper/snake9_research.tex').write_bytes(EDITOR.read_bytes())
print({'before_lines':len(source.splitlines()),'after_lines':len(s.splitlines()),'bytes':len(EDITOR.read_bytes())})
