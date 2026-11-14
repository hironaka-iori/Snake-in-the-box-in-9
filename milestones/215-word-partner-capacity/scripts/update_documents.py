"""Add the source-specific word-capacity argument to the existing manuscripts."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
s=json.loads((H/'data/search-summary.json').read_bytes())
assert json.loads((H/'data/PathWordCapacity215-audit.json').read_bytes())['status']=='PASS'
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=H/'data'/('before-'+name);assert not p.exists();p.write_bytes((D/name).read_bytes())
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
front=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=main.replace('Research state after round 214, 15 November 2026','Research state after round 215, 15 November 2026',1)
front=front.replace('Research state after round 214','Research state after round 215',1)
front=front.replace('Its group rule is a possible stronger search step; only the\nzero-support and exhausted-allowance rules are implemented here.',
    'At round 212, only the zero-support and exhausted-allowance rules\nwere implemented; the group rule is incorporated in round 214 below.',1)
front=front.replace('The new continuation examines 749,506 additional nodes and records\n3,054 value removals by this rule. Thirteen regions remain unfinished;',
    'The round-214 continuation examines 749,506 additional nodes and records\n3,054 value removals by this rule. Thirteen regions remain unfinished\nat that cutoff;',1)
text=r'''
\subsection{Actual word capacity in every interval family}
\label{sec:word215}
Partner capacity counts possible sharing relations. It can overlook
competition for the actual word labels. The chosen and outside
families each have distinct words, so a second necessary condition
applies separately to all four parity families.

\begin{proposition}[Domain capacity from the reconstructed path]\label{prop:word215}
Let $F$ be one of the chosen or outside families in the saved $(0,6)$
construction, let $J\subseteq F$, and let $U$ contain every currently
allowed word of each interval in $J$. Every reconstructed induced
path fitting these domains satisfies $|J|\le |U|$.
If $|J|=|U|$, every interval of $F\setminus J$ must avoid $U$.
Removing those words preserves the same complete assignment.
\end{proposition}
\begin{proof}
The geometric partner argument gives distinct assigned words throughout
$F$. In particular, the words assigned to $J$ inject into $U$, proving
the inequality. At equality they use all of $U$. Each remaining member
of $F$ has a word distinct from all of them, so its value survives
the stated deletion. Other values and all path conditions are unchanged.
\end{proof}

The checked composition derives both subset distinctness and the required
conflicts from the actual indexed-path premise. Unlike the spare-capacity
argument, this implication requires no normalization at zero, raw-value
bound, fixed alphabet cardinality or assumption that a full parity
alphabet is occupied. Current-domain fitting and containment in $U$
remain explicit. It applies when a small part of an otherwise
unsaturated family has exhausted its available words.

The native engine combines this condition with tight partner capacity.
A word matching proposes a subset. A deficient union is counted
directly before rejection; for a tight subset, the current domain
union is recomputed before deletion. Filtering remains within one
chosen or outside family, because words may legitimately be shared
between the two families. Previously proved finite counting lemmas
are reused; this is an application of established distinct-value
reasoning, with a checked connection to the specific snake construction.
Native execution and complete traversal retain their separate
verification status~\cite{research215}.

'''
t=s['new_operation_totals']
text+=('The separate continuation accepted '+str(s['new_jobs'])+' new jobs and examined '
       +format(t['nodes'],',')+' additional nodes. The added word-capacity rule recorded '
       +format(t['word_subset_removals'],',')+' value-removal operations and '
       +format(t['word_subset_failures'],',')+' contradiction returns. '
       +'These are repeated operations across branches; they do not establish a speed improvement.\n')
if s['status']=='OPEN':
    text+=('The case remains open with '+str(s['pending'])+' unfinished regions. '
           +'No new parent class, longer snake or complete coordinate-case exclusion is obtained.\n\n')
elif s['status']=='EXHAUSTED':
    text+=('The saved model is exhausted. This is a native exclusion for the fixed source, '
           +'retained coordinates, normalization and model; it supplies no universal '
           +'exclusion of 98-edge parents or longer nine-dimensional snakes.\n\n')
else:raise RuntimeError('Inspect and describe the witness before updating the paper.')
text+=r'''A further comparison considers all maximal same-parity families whose
words must be distinct. Each contains every multi-visit interval and
one complete singleton family from each opposite corner pair. The saved
model has four such families per parity. On the thirteen inherited
regions, a single pass appears to give 35 extra deletions. After the
existing four-family and binary rules reach closure, twelve regions
admit no further deletion by these maximal families; the remaining
region is already deficient under the existing rules. Thus this
snapshot supplies no evidence of additional propagation strength.
The comparison is a separate finite-domain calculation, without a
new path exclusion or a checked implementation of mixed-family rules.

'''
anchor='\\section{Verification scope and remaining problem}\\label{sec:verification}'
assert main.count(anchor)==1;main=main.replace(anchor,text+anchor,1)
bib=r'''
\bibitem{research215}
Snake-in-the-box project. \emph{Combining actual-word capacity and partner
capacity in the retained-coordinate construction}. Research milestone
215, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/215-word-partner-capacity}.

'''
main=main.replace('\\end{thebibliography}',bib+'\\end{thebibliography}',1)
brief=r'''
\paragraph{Actual words must also fit.}
Possible partners do not resolve competition for word labels.
Within any one chosen or outside family, a subset $J$ requires
distinct words in its domain union $U$. Thus $|J|\le|U|$; equality
reserves all of $U$ for $J$, and the other members of that family
must avoid it. The geometric path condition supplies the distinctness.
Lean now checks this composition and preservation of the same assignment
for all four families, without requiring a saturated parity alphabet.
The new continuation combines this rule with partner capacity.
'''
brief+=('It examines '+format(t['nodes'],',')+' additional nodes and records '
        +format(t['word_subset_removals'],',')+' word-removal operations by the added rule.\n')
brief+=('The case remains open with '+str(s['pending'])+' unfinished regions.\n\n' if s['status']=='OPEN' else
        'The fixed source-specific model is exhausted, with native traversal certification still separate.\n\n')
brief+=r'''The four maximal distinct-word families of each parity supply a
possible extension. On the thirteen inherited regions, however,
their apparent additional deletions disappear after the existing
family and binary rules reach closure. This comparison gives no
evidence that adding those families improves the search.

'''
front=front.replace('\\section{What would resolve the question}',brief+'\\section{What would resolve the question}',1)
front=front.replace('milestones through round 214','milestones through round 215',1)
for name,source in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
    (D/name).write_text(source,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes((D/name).read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS')
