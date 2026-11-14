"""Update the existing editor manuscripts after the saved continuation ends."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
s=json.loads((H/'data/search-summary.json').read_bytes())
assert s['status']=='OPEN', 'Inspect any witness or complete exclusion before writing conclusions.'
for name in ['TwoStep216','Joint216','PathJoint216','LiteralJoint216']:
    assert json.loads((H/'data'/(name+'-audit.json')).read_bytes())['status']=='PASS'
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    backup=H/'data'/('before-'+name);assert not backup.exists();backup.write_bytes((D/name).read_bytes())
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
front=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=main.replace('Research state after round 215, 15 November 2026','Research state after round 216, 15 November 2026',1)
front=front.replace('Research state after round 215','Research state after round 216',1)
main=main.replace('The case remains open with 5 unfinished regions.','At the round-215 cutoff, the case remains open with five unfinished regions.',1)
front=front.replace('The case remains open with 5 unfinished regions.','At the round-215 cutoff, the case remains open with five unfinished regions.',1)
text=r'''
\subsection{Joint support among successive free-word groups}
\label{sec:joint216}
Capacity restrictions concern distinct values within families. A different
restriction uses the simultaneous compatibility of three groups.

\begin{lemma}\label{lem:two-step216}
If $u,v,w\in Q_r$ satisfy $d(u,v)=d(v,w)=1$, then
$d(u,w)\in\{0,2\}$. If $u\ne w$, then $d(u,w)=2$.
\end{lemma}
\begin{proof}
Each step flips one coordinate. Flipping the same coordinate twice
returns to $u$; flipping different coordinates changes exactly two.
\end{proof}

The reconstructed path supplies one free-coordinate edge between each
successive pair of groups. The lemma therefore applies to groups
$g,g+1,g+2$. The zero-distance possibility must be retained unless
their decoded outer words are known to differ. Inequality of unbounded
integer labels alone would not justify removing it.

\begin{proposition}[Preserving jointly supported pairs]\label{prop:joint216}
Let $A,B,C$ be three current word domains, with necessary binary
relations $R_{AB},R_{BC},R_{AC}$. Retain a pair $(a,b)\in R_{AB}$
only if some $c\in C$ satisfies both $(b,c)\in R_{BC}$ and
$(a,c)\in R_{AC}$. Apply the analogous restriction to the other
two relations. Every fitting complete assignment survives these
restrictions. They remain valid for every subsequent subdomain of
the domains used to derive them.
\end{proposition}
\begin{proof}
The actual third value of any fitting assignment witnesses the
required support for each of its three assigned pairs. Thus each
restriction preserves that same assignment. Repetition preserves
the statement by induction. An assignment in smaller domains also
belongs to the original domains, so it has the same support witness.
\end{proof}

Independent support can miss this restriction. In one analyzed region,
the outer words 5 and 6 are allowed and have distance two. Their only
common six-bit neighbours are 4 and 7, both absent from the middle
domain. Nevertheless, 5 has available middle neighbours 21 and 37,
while 6 has 22 and 38. The pair $(5,6)$ is therefore impossible even
though neither value is individually unsupported. The two common
neighbours and the stated support distinction have finite Lean checks.

On the five inherited regions, binary propagation and the four-family
capacity rules reach a fixed point. The additional distance-zero-or-two
condition removes no individual value. Joint support then excludes
940 pair occurrences, including 44 occurrences on consecutive pairs.
Installing one projection pass and repeating those existing rules
still removes no individual value. These are occurrences across
regions and triples, without a count of distinct global exclusions.
The comparison omits partner, lexicographic and higher-order exclusion
rules, so it does not reproduce the entire native propagation.

The continuation retains the projected pair restrictions during later
branching. It derives them only at the beginning of a submitted job,
after ordinary propagation, using at most four sweeps. Descendant
domains only shrink, and the original relations are reloaded for each
new job. These conditions permit restrictions derived from the initial
domains to remain in force throughout that job. Four sweeps bound the
work; no closure claim is made. The checked pair-preservation argument
and the actual-path composition retain explicit domain and outer-relation
premises. Native table interpretation and complete execution remain
separate verification obligations~\cite{research216}.

'''
t=s['new_operation_totals']
text+=('The continuation accepts '+str(s['new_jobs'])+' new jobs and examines '
       +format(t['nodes'],',')+' additional nodes. The new rule records '
       +format(t['joint_pair_removals'],',')+' pair-removal operations. '
       +'These repeated operations do not establish a speed improvement. '
       +'The case remains open with '+str(s['pending'])+' unfinished regions; '
       +'no new parent, longer snake or complete coordinate-case exclusion is obtained.\n\n')
anchor='\\section{Verification scope and remaining problem}\\label{sec:verification}'
assert main.count(anchor)==1;main=main.replace(anchor,text+anchor,1)
bib=r'''
\bibitem{research216}
Snake-in-the-box project. \emph{Joint word support and two-step geometry
in the retained-coordinate construction}. Research milestone 216,
15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/216-joint-word-support}.

'''
main=main.replace('\\end{thebibliography}',bib+'\\end{thebibliography}',1)
brief=r'''
\paragraph{Pairs need a common third value.}
Two successive free-coordinate steps leave the outer words at distance
zero or two: the two flipped coordinates are equal or different.
The reconstructed path supplies these successive edges, and Lean checks
the resulting implication. Distinct decoded outer words force distance two.

More information comes from the middle domain. Outer words 5 and 6
have only common neighbours 4 and 7. If both are unavailable, the pair
cannot occur, even when each outer word has other available neighbours.
For each of three pair relations, retaining only pairs with a compatible
third value preserves every fitting assignment: its actual third value
is the witness. The same restriction remains valid in smaller domains.
This reasoning and the concrete support example are checked in Lean.

The five-region comparison finds 940 unsupported pair occurrences
without removing an individual word. It omits some native rules and
establishes no speed advantage. The continuation therefore retains
the pair information during later branching, deriving it only at each
job's start and reloading the original relations for every new job.
Native execution and full search certification remain separate.
'''
brief+=('The new continuation examines '+format(t['nodes'],',')+' nodes and records '
        +format(t['joint_pair_removals'],',')+' repeated pair-removal operations. '
        +'The model remains open with '+str(s['pending'])+' unfinished regions.\n\n')
front=front.replace('\\section{What would resolve the question}',brief+'\\section{What would resolve the question}',1)
front=front.replace('milestones through round 215','milestones through round 216',1)
for name,source in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
    (D/name).write_text(source,encoding='utf-8',newline='\n')
    (R/'paper'/name).write_bytes((D/name).read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS')
