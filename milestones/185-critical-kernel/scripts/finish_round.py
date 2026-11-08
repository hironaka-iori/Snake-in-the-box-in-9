"""Save the exact end-of-round proof boundary and update existing documents."""
from pathlib import Path
import json,hashlib,datetime,re,sys
R=Path('E:/Snake-in-a-box');H=R/'milestones/185-critical-kernel'
sys.path.insert(0,str(H/'scripts'));import native_resources as nr
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
 p=str(Path(p))
 if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[p]
def js(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
snap=nr.snapshot();assert not snap['errors'] and not snap['processes'],snap
order=read(H/'data/current-order.json');accepted=[];reports=[]
for name in order:
 p=H/'data'/(name+'-audit.json')
 if not p.exists():continue
 j=read(p);assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
 for a,b in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(j[a])==j[b],j[a]
 for q,d in j['dependencies'].items():assert sha(q)==d,q
 accepted.append(name);reports.extend(j['axioms'])
assert 'LocalWindowTagsShare185' in accepted
assert not any(x.startswith('Share185.Shard') for x in accepted)
failures=[]
for p in sorted((H/'logs').glob('*/record.json')):
 j=read(p)
 if j['status']!='PASS':
  failures.append({'module':j['module'],'reason':j['stop_reason'],'exit_code':j['exit_code'],
   'record':str(p.relative_to(H)),'source_sha256':j['source_sha256'],
   'peak_private':max((x['PrivatePageCount'] for v in j['resource_samples'] for x in v['processes'] if x['ProcessId']==j['compiler_pid']),default=0)})
cnf=H/'certificates/share185.cnf'
assert sha(cnf)==sha(R/'milestones/183-critical-floor15/cache/012034-floor15-dense.cnf')
j=dict(round=185,status='COMPLETE_ROUND_GENERIC_PERMUTATION_CHECKER; CONCRETE_INTERPRETATION_PENDING',
 pause_requested=True,next_round_started=False,timed_phase_start_utc='2026-11-08T14:24:44+00:00',
 closed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),generic_checker_Lean_checked=True,
 planned_current_modules=len(order),accepted_modules=len(accepted),accepted_module_names=accepted,
 theorem_dependency_reports=reports,concrete_clause_batches_checked=0,concrete_clause_batches_total=98,
 core_clauses=12424,dense_variables=5342,semantic_variables=5906,exact_dense_cnf_sha256=sha(cnf),
 remaining=[n for n in order if n not in accepted],full_initial_database_truth=False,
 critical_Lean_refutation=False,new_unconditional_bound=False,failures=failures,resource_snapshot=snap,
 validated_unique_dependency_files=len(cache))
js(H/'data/completion.json',j)
(H/'scripts/finish_round.py').write_bytes(Path(__file__).read_bytes())
(H/'scripts/publication.py').write_text((R/'milestones/184-single-critical-floor/scripts/publication.py').read_text().replace('Round184','Round185'),newline='\n')
(H/'.gitattributes').write_bytes((R/'milestones/184-single-critical-floor/.gitattributes').read_bytes())
note=r"""\paragraph{Reordering threshold terms in the critical certificate.}
The streamed $012034$ input appends the fifteenth threshold bit for each
of its 35 corner occurrences after the first fourteen layers. The earlier
clause checker required the threshold terms in a fixed order. Its
soundness proof now allows any permutation of those terms, preserving
multiplicities. Indeed, for nonnegative integer corner shares $s_j$,
\[
\sum_{j=1}^{35}\sum_{t=1}^{15}\mathbf{1}_{\{t\le s_j\}}
 =\sum_{j=1}^{35}\min(s_j,15)\le\sum_{j=1}^{35}s_j.
\]
A permutation preserves the left-hand count. Thus a physical window
share at most fourteen permits an assignment satisfying the cap clause,
which negates the counter output for at least fifteen true terms.
The internal counter implications follow from
$i\le A$ and $j\le B$ implying $i+j\le A+B$ for the two child counts.
The selected-vertex, endpoint and empty-square assumptions are unchanged.

The generalized counting lemma and clause-soundness theorem pass Lean.
The reconstructed input also matches all 12,424 clauses of the saved
dense core exactly. Its complete concrete interpretation is still
pending: the counter and totalizer structure checks exceed the existing
256 MiB limit when checked as single propositions. Splitting constant
data and supplying explicit meaning trees has not removed that
obstruction. No concrete clause batch or final contradiction was
accepted in this round. The next step is to prove those structural
conditions in smaller parts, then check the 98 clause batches and their
composition. The numerical bound 234 retains its stated assumptions.

"""
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=Path('D:/Codex/2026-10-13/new-chat/outputs')/name;mirror=R/'paper'/name
 original=p.read_text(encoding='utf-8');assert p.read_bytes()==mirror.read_bytes()
 backup=H/'source-before'/name;backup.parent.mkdir(exist_ok=True);assert not backup.exists();backup.write_bytes(p.read_bytes())
 marker=(r'\section{Remaining requirements for a stronger bound}\label{sec:closure}' if name=='snake9_research.tex' else r'\textbf{6. What is proved, and what remains.}')
 assert original.count(marker)==1
 result=original.replace(marker,note+marker)
 if name=='snake9_frontier_explanation.tex':result=result.replace('Research state after round 184','Research state after round 185')
 assert re.findall(r'\\author\{[^\n]*',result)==re.findall(r'\\author\{[^\n]*',original)
 assert re.findall(r'\\hypersetup\{.*?\n\}',result,re.S)==re.findall(r'\\hypersetup\{.*?\n\}',original,re.S)
 p.write_text(result,encoding='utf-8',newline='\n');mirror.write_bytes(p.read_bytes())
readme=f"""# Round 185: permutation-invariant cap semantics

This round completes the request for one 15–25 minute round and then a pause. Pause after publication. Do not start round 186 without a new instruction.

The result is a Lean-checked generalization of the share-clause soundness theorem. The streamed critical floor-15 certificate lists fourteen threshold layers first and appends the fifteenth layer. The previous checker required a fixed order. The new checker accepts a permutation of the threshold pairs, with multiplicities preserved. Permutation preserves the number of true threshold terms; each corner contributes at most its physical integer share. All other local hypotheses remain unchanged.

The general counting, clause-soundness and refutation-composition implications passed Lean. The current dependency order has {len(order)} modules, of which {len(accepted)} are accepted. These contain generic proofs and exact constant data. **Zero of the 98 concrete clause batches has been checked.** Initial-database truth and the critical Lean contradiction remain incomplete.

## Exact input and proof boundary

The generated CNF is byte-identical to the round-183 dense input: 12,424 clauses, 5,342 proof variables and SHA-256 {sha(cnf)}. Interpretation uses 5,906 variables, including auxiliary meanings needed to validate counters. No input clause was weakened or removed. The native refutation remains the separately replayed 52,489-deduction proof from round 183.

The generic checker has accepted dependency reports for cap_total, soundS and refutedShare_of_check. These are implications under structural and local-model conditions. They do not establish that the concrete input satisfies those conditions.

## Resource obstruction and preserved attempts

The existing limits were retained: 1 GiB free memory before a core Lean check, 256 MiB private memory and a 768 MiB free reserve. No heavy worker remains. Failed attempts and exact source snapshots are in logs/.

Splitting general proofs into individual lemmas and splitting raw clauses and tags into smaller data modules succeeded. Explicit small meaning trees also compiled. However, both isolated Share185.Counts and Share185.Totals still exceeded the memory limit. No structural theorem was accepted; the 98 dependent clause batches and final composition were not run.

Generated documentation fragments, tuple syntax and the Boolean-equality-instance proof were corrected before acceptance. Their failed logs remain. Superseded sources are retained; data/current-order.json specifies the current dependency order.

## Mathematical consequence

The round-184 profile (15,14,14,14) and comparison 42254m + 45L <= 9928453 remain unchanged. They yield conditional 234 using nonnegative loss. This round removes the general order restriction from the checker, but does not discharge the concrete local-share premise or any inherited graph premise.

The maintained project range remains 191–235, with the archived 235 proof's complete independent rebuild pending. The optimum, 196 and an unconditional improvement are unresolved.

## Resume point

1. Read data/completion.json and data/current-order.json.
2. Divide concrete counter and totalizer conditions into smaller proved components, including individual literal conditions where needed. Preserve the original local assumptions and exact dense CNF.
3. Finish the 98 concrete clause checks and Share185.Compose.
4. Check the compact critical contradiction in Lean and connect it to actual snakes using the existing geometric bridge.

Do not repeat the native solver, completed generic proofs or old share-18 replay. The older replay remains at 33,111 of 145,215 deductions and is separate. Inspect live process handles before resuming a worker. Keep the guards, hashes and failed attempts.

The existing D: manuscript and short explanation are updated in place and mirrored under paper/. Authors and hypersetup are preserved. Full manuscript review is due in round 186, after the pause.
"""
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
status=f"""# Round 185 complete; pause after publication

The user requested one 15–25 minute round and then a pause. Round 185 is complete. Do not start round 186 without a new instruction.

Lean checked the generalized cap-counting and share-clause soundness theorem with permutations of threshold terms, preserving multiplicities. This addresses the ordering of the streamed 012034 input, where the fifteenth layer is appended after the first fourteen layers.

The dense CNF is unchanged: 12,424 clauses and 5,342 proof variables. Interpretation uses 5,906 variables. There are {len(accepted)} accepted modules among {len(order)} current modules, covering generic proofs and constant data. Zero of 98 concrete clause batches has passed. Isolated Counts and Totals checks still exceed the unchanged 256 MiB private-memory cap. No initial-database truth, final contradiction or actual-snake floor-15 theorem is claimed.

The comparison remains 42254m + 45L <= 9928453, yielding conditional 234 from profile (15,14,14,14) and inherited local and graph premises. No unconditional improvement was obtained. The project range remains 191–235, with the archived 235 proof's independent rebuild pending.

Read milestones/185-critical-kernel/README.md, data/completion.json and data/current-order.json. Next: prove concrete structural conditions in smaller parts; complete 98 clause batches and composition; then complete the compact Lean contradiction and geometric transfer. The native critical proof has 52,489 deductions and should not be regenerated.

The hypothetical 0123104 six-count floor 25, reference/context exclusions, graph coverage and complete finite-edge proof remain unresolved. The old share-18 replay remains separate at 33,111/145,215 deductions. Preserve authors, hypersetup, D: sources, E: mirrors, unrelated changes and failure evidence. Full manuscript review is due in round 186.
"""
(R/'handoff/CURRENT_STATUS.md').write_text(status,newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text("""# Resume only after a new instruction

Round 185 has finished and the user requested a pause. Do not start round 186 automatically.

Read CURRENT_STATUS.md and milestones/185-critical-kernel/README.md. The permutation-aware generic checker is Lean-checked. Concrete Counts and Totals are the immediate obstruction: each exceeded the 256 MiB private-memory cap. Divide them into smaller logical components before running the 98 concrete clause batches. Zero of those batches is accepted. Use the saved source order and exact receipts; do not restart completed generic proofs or the native solver.

The reduced critical CNF remains byte-identical to round 183. Preserve clause and variable mappings. After initial-database truth is proved, complete its 52,489-deduction Lean refutation and geometric transfer. The older share-18 proof is separate.

Keep core startup at 1 GiB, private memory at 256 MiB and free reserve at 768 MiB. Keep the separate Mathlib profile unchanged. Inspect live processes before starting one sequential worker. Preserve failures and exact audited bytes.

Check GitHub before research. Update the existing D: LaTeX sources and E: mirrors while preserving authors and hypersetup. Full manuscript review is due in round 186. Conditional 234 and the qualified range 191–235 remain unchanged; no unconditional improvement or optimality is established.
""",newline='\n')
p=R/'README.md';old=p.read_text()
p.write_text("""# Current result after round 185

The requested round is complete; research pauses after publication. Lean checked the permutation-aware cap-counting and share-clause soundness theorem for the streamed critical certificate. Concrete counter and totalizer checks remain unfinished because they exceed the unchanged memory limit. Zero of 98 concrete clause batches has passed.

The conditional bound remains 234 with profile (15,14,14,14). No new unconditional numerical bound is claimed. Read [round 185](milestones/185-critical-kernel/README.md), [the current handoff](handoff/CURRENT_STATUS.md), [the main manuscript](paper/snake9_research.tex) and [the short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

"""+old,newline='\n')
print('ROUND_185_SAVED',len(accepted),'accepted modules;',len(order)-len(accepted),'pending; 0/98 concrete clause batches.')

