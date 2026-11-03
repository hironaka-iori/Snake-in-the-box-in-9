"""Record the completed count theorem in the existing paper and current handover."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/total115-completion.json')['status']=='PASS_COMPLETE_TOTAL115_RECEIPT_AND_DEPENDENCY_AUDIT'
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');q=R/'paper/snake9_research.tex'
raw=p.read_bytes();assert raw==q.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='085c3c21dfce979061464888f9ee4ce59b62fced00714a70a8e912426d0b74bd'
s=raw.decode('utf-8')
start=s.index('The $012314$ row is Theorem~\\ref{thm:outer-four-sum}. The other rows remain')
end=s.index('\nThe remaining proposed restrictions have native solver exclusions',start)
s=s[:start]+r'''The $012314$ row is Theorem~\ref{thm:outer-four-sum}. The following theorem
establishes the $012310$ row without additional count or parity assumptions.

\begin{theorem}\label{thm:012310-total19}
Let $x_0,\ldots,x_m$ be a snake in $Q_9$. If its six-transition segment
starting at $x_r$ has canonical direction word $012310$ and $r+6\le m$, then
\[
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+3}+\alpha_{r+4}+\alpha_{r+5}\ge19.
\]
\end{theorem}
\begin{proof}
Translate the first vertex to zero and permute coordinates to obtain the
canonical window. Assign the selected-vertex and endpoint indicators from
the full snake. These assignments satisfy the local induced-path conditions,
and the five local corner counts equal the five displayed counts.
If their sum were at most $18$, the concrete count encoding would give
a satisfying assignment of its retained $5067$-clause core. A checked
refutation with $287753$ deductions and $16816989$ propagation references
ends in the empty clause, giving a contradiction. The complete replay,
count interpretation and arbitrary-snake deduction have passed Lean.
The final statement requires only the fitting direction window.
\end{proof}

The preserved completion covers all $1397$ proof modules, including the
final deduction above. A fresh audit checks their source, object, log and
dependency hashes, with only the standard accepted axioms. The full input
has $5114$ clauses; its five counters retain $105$ corner occurrences
involving $84$ distinct corners~\cite{criticalcountarchive,totalcountarchive,share145archive}.
This discharges one local premise in the finite comparison. It gives no
new global bound by itself. The other rows, apart from the two proved
above, remain unproved for arbitrary snakes in the current Lean development.
For $012340$ with middle count at most two, an independent native refutation
supports $22$; its concrete interpretation and Lean replay remain unfinished.
''' + s[end:]
anchor='A further local theorem shows that alternate internal counts $3,4,3$ in a $012032$ window force one intervening count to be at least six.'
assert s.count(anchor)==1
s=s.replace(anchor,anchor+' The five internal counts of a canonical $012310$ window sum to at least $19$.')
new=s.encode('utf-8');assert new.split(b'\\begin{document}',1)[0]==raw.split(b'\\begin{document}',1)[0]
p.write_bytes(new);q.write_bytes(new)
rev=read(H/'data/paper-revision.json');rev['two_cycle_intermediate_sha256']=rev['after_sha256'];rev['after_sha256']=hashlib.sha256(new).hexdigest()
rev['completed_local_theorem']='012310 five internal counts sum to at least19'
(H/'data/paper-revision.json').write_text(json.dumps(rev,indent=2)+'\n')
addition='''The separate count-sum proof is now complete: all 1,397 modules passed,
including the theorem that the five internal counts of every fitting
canonical 012310 window sum to at least 19. A fresh audit verified the
recorded sources, objects, logs and dependencies. Exact successful receipts,
source snapshots and checker snapshots are archived in three verified parts.
This discharges one local premise and gives no new global bound by itself.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    f=R/name;text=f.read_text(encoding='utf-8');assert text.startswith('# Research update: milestone 145\n\n')
    text=text.replace('# Research update: milestone 145\n\n','# Research update: milestone 145\n\n'+addition,1);f.write_text(text,encoding='utf-8')
f=H/'README.md';text=f.read_text(encoding='utf-8');f.write_text(text.replace('# Research update: milestone 145\n\n','# Research update: milestone 145\n\n'+addition,1),encoding='utf-8')
f=R/'handoff/NEXT_AGENT_PROMPT.md';text=f.read_text(encoding='utf-8')
text+='''
Completion update:115 is now PASS_COMPLETE_TOTAL_COUNT_PROOF,1397/1397,
including ActualTotal115.actual_total_sum. This is an arbitrary-snake
canonical012310 five-count sum>=19 theorem, with no extra count/parity
hypotheses.145/data/total115-completion.json freshly verifies every receipt,
source/object/log hash and recorded dependency. Exact successful receipts,
logs, source and checker snapshots are in three archive parts, with a safe
restore script. No115 driver needs resuming. This discharges one inherited
local premise only. Other global assumptions and graph assembly remain.
''';f.write_text(text,encoding='utf-8')
f=H/'MATHEMATICAL_NOTE.md';text=f.read_text(encoding='utf-8')
text+='''
## Completed count-sum theorem

The separate milestone 115 batch completed all 1,397 modules during this
round. For every fitting canonical direction window 012310 in any snake,

\\[
\\alpha_{r+1}+\\alpha_{r+2}+\\alpha_{r+3}+\\alpha_{r+4}+\\alpha_{r+5}\\ge19.
\\]

The final theorem has no additional count, endpoint-location or parity
hypotheses. Its complete Boolean replay has 287,753 deductions and
16,816,989 references; the actual-snake interpretation also passed Lean.
The completion audit rechecked every successful source, object, log,
source snapshot, checker snapshot and recorded dependency. This is a fresh
verification of saved results, with no compiler rerun. Exact records are
archived in three ordered parts under certificates/; the original archive
and all original records remain locally. This completes one inherited local
premise, while the global bound is unchanged.
''';f.write_text(text,encoding='utf-8')
print(rev['after_sha256'])
