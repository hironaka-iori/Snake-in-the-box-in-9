from pathlib import Path
import hashlib, json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
D = Path('D:/Codex/2026-10-13/new-chat/outputs')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

main_addition = r'''
\subsection{Trading a weaker share floor against positive loss}
\label{sec:floor14-loss}
The preceding least-floor statement assumes only $L\ge0$. Positive loss
permits a weaker local requirement without recomputing the potential.
If every pending floor decreases by one, each edge weight decreases by
at most one. Indeed, the weight is the maximum of a fixed source bound
and a count term plus the maximum of the share floor and a fixed
count-conditioned bound, followed by an unchanged additional credit.
Each maximum preserves the one-unit bound. Thus the same potential
satisfies an edge inequality whose scaled mean is nine smaller.

\begin{proposition}[Sufficient loss for floor fourteen]
Retain the graph, count restrictions, completed floors and interpretation
premises of Section~\ref{sec:boundary-retuning}. Then either of the
following sets of additional premises implies $m\le234$:
\begin{enumerate}
\item the four pending local share floors are at least fourteen and $L\ge23$;
\item the $012034$ floor is at least fourteen, the other three pending
floors are at least sixteen, and $L\ge17$.
\end{enumerate}
\end{proposition}
\begin{proof}
For the first case, reuse the potential for $(15,15,15,15)$. Its scaled
mean becomes 4444 and its scaled range remains 5384. Summing along
$m-8$ transitions gives $4444(m-8)\le9W+5384$. Combining this with
$W+4200m+5L\le1098600$ yields
\[
42244m+45L\le9928336.
\]
At $m=235$, this requires $45L\le996$, hence $L\le22$.
For the second case, reuse the potential for $(15,16,16,16)$, with
scaled mean 4445 and scaled range 5374. The same calculation gives
\[
42245m+45L\le9928334.
\]
At $m=235$ it requires $45L\le759$, hence $L\le16$.
Larger lengths only strengthen both contradictions.
\end{proof}

The weight transfer and both arithmetic deductions pass Lean. They use
the previously scanned finite potentials; no new edge scan or complete
Lean graph certificate is asserted. The loss thresholds 23 and 17 are
exact for these reused comparisons, but their optimality over other
potentials is unresolved. At scaled mean 4448, an improved floor-fourteen
potential with scaled range $R_{\mathrm{sc}}$ would suffice whenever
$R_{\mathrm{sc}}+1\le5296+45L$. In particular, range at most 5340
would suffice with $L\ge1$. The saved walk forces range at least 5310
at that mean; it does not establish the existence of such a potential.
A fresh computation was prevented from starting by the established
memory threshold, so this possibility remains open.

This gives a precise case reduction for the uniform-floor route. If
floor fourteen and the retained graph premises can be proved universally,
the stronger floor fifteen is needed only for hypothetical 235-edge
snakes with $L\le22$. Every such snake dominates the cube, since an
undominated vertex contributes at least 96 to $L$. No claim that the
remaining low-loss case is impossible follows from this reduction.

'''

short_addition = r'''
\textbf{5. A weaker floor when the loss is positive.}
Lowering each pending floor by one decreases any edge weight by at most
one: all other terms stay fixed, and taking a maximum preserves this
bound. Therefore the saved potential still works after its scaled mean
decreases by nine. Reusing the two potentials above gives
\[
\begin{array}{c|c|c}
\text{floors}&\text{resulting inequality}&\text{sufficient loss}\\\hline
(14,14,14,14)&42244m+45L\le9928336&L\ge23\\
(14,16,16,16)&42245m+45L\le9928334&L\ge17
\end{array}
\]
At $m=235$, the first inequality forces $L\le22$, and the second forces
$L\le16$. This proves both sufficient thresholds. The transfer and
arithmetic pass Lean; all local and graph premises remain explicit.
These thresholds are sufficient and have not been optimized over new
potentials. A fresh optimization did not start because insufficient
memory was available. At scaled mean 4448, range at most 5340 would
make $L\ge1$ sufficient, but such a potential has not been obtained.

Consequently, if the four floor-fourteen bounds and graph premises are
established, the stronger floor-fifteen argument need only address
$L\le22$. Those snakes dominate the cube by the existing 96-loss
bound for an undominated vertex. The low-loss case remains unresolved.

'''

for name in ['snake9_research.tex', 'snake9_frontier_explanation.tex']:
    p = D/name
    mirror = R/'paper'/name
    assert p.read_bytes() == mirror.read_bytes(), 'Editor and repository differ'
    raw = p.read_bytes()
    (H/'data'/(name+'.before.txt')).write_bytes(raw)
    s = raw.decode('utf-8')
    if name == 'snake9_research.tex':
        anchor = '\\section{Remaining requirements for a stronger bound}'
        assert s.count(anchor) == 1
        s = s.replace(anchor, main_addition+anchor)
    else:
        s = s.replace('Research state after rounds 175--176', 'Research state after round 177')
        s = s.replace('\\textbf{5. What is proved, and what remains.}', short_addition+'\\textbf{6. What is proved, and what remains.}')
        s = s.replace('Research pauses\nafter these two rounds as requested;', 'Research pauses\nafter round 177 as requested;')
        s = s.replace('research records 175--176.', 'research records 175--177.')
    p.write_text(s, encoding='utf-8', newline='')
    mirror.write_bytes(p.read_bytes())

inputs = {}
for rel in [
 'milestones/176-boundary-retuning/data/graph-joint15/floor15.json',
 'milestones/176-boundary-retuning/data/graph-final/floor15.json',
 'milestones/176-boundary-retuning/lean/FinalBoundary176.lean',
 'milestones/175-physical-share-loss/data/BoundaryPacking175-audit.json',
 'milestones/175-physical-share-loss/data/ShareLoss172-audit.json']:
    inputs[rel] = sha(R/rel)
for folder in ['graph-joint15', 'graph-final']:
    path = R/'milestones/176-boundary-retuning/data'/folder
    j = json.loads((path/'floor15.json').read_text())
    assert j['status'] == 'PASS_POTENTIAL'
    assert j['scan']['edges'] == 4661572 and j['scan']['violations'] == 0
    archive = path/j['potential_file']
    assert sha(archive) == j['potential_archive_sha256']
    inputs[str(archive.relative_to(R))] = sha(archive)
j = json.loads((H/'data/LossTradeoff177-audit.json').read_text())
assert j['status'] == 'PASS' and len(j['axioms']) == 8
out = {
 'round':177, 'status':'COMPLETE_CONDITIONAL_TRADEOFF',
 'new_unconditional_bound':False, 'maintained_project_interval':[191,235],
 'upper235_full_independent_rebuild':'pending',
 'uniform14_sufficient_loss':23, 'single14_other16_sufficient_loss':17,
 'new_full_edge_scan':False, 'optimal_loss_threshold':'unresolved',
 'lean_modules':1, 'lean_dependency_reports':8, 'input_pins':inputs,
 'documents':{str(p.relative_to(R)):sha(p) for p in (R/'paper').glob('snake9_*.tex')},
 'pending':'Local floors, inherited count restrictions and exclusions, complete graph-to-snake and Lean graph certificates.',
 'partial_share18_replay':[33111,145215],
 'retuning_attempt':{'status':'NOT_STARTED_RESOURCE_GATE','free_bytes':1217253376,
 'required_free_bytes':2147483648,'child_started':False},
 'pause_requested':True
}
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Saved round 177 and updated both existing documents')
