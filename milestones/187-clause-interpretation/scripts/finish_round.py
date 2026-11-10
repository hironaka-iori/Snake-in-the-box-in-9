"""Close the round at its actual checked boundary and update the existing documents."""
from pathlib import Path
import datetime,hashlib,json,re,sys
R=Path('E:/Snake-in-a-box');H=R/'milestones/187-clause-interpretation'
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
sys.path.insert(0,str(H/'scripts'));import native_resources
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=str(p)
    if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
    return cache[p]
def audit(p):
    j=read(p);assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None,p
    for k,d in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
        assert sha(j[k])==j[d],j[k]
    for q,d in j['dependencies'].items():assert sha(q)==d,q
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
    return j
snap=native_resources.snapshot();assert not snap['processes'] and not snap['errors'],snap
for p in (H/'data').glob('run-*.json'):assert read(p)['status']!='RUNNING',p
order=read(H/'data/current-order.json');accepted=[];reports=0
for n in order:
    p=H/'data'/(n+'-audit.json')
    if p.exists():j=audit(p);accepted.append(n);reports+=len(j['axioms'])
for n in ['Combined187','BoundarySlack187','BoundarySlackCases187']:assert n in accepted,n
old=R/'milestones/186-structural-interpretation';oldnames=read(old/'data/completion.json')['accepted_module_names']
for n in oldnames:audit(old/'data'/(n+'-audit.json'))
prior=[]
for folder,names in [('175-physical-share-loss',['SixPacking175','SixPrefixBoundary175']),('171-empty-square-count',['LossDomination171'])]:
    for n in names:
        p=R/'milestones'/folder/'data'/(n+'-audit.json');audit(p)
        prior.append({'receipt':str(p),'sha256':sha(p)})
cnf=R/'milestones/185-critical-kernel/certificates/share185.cnf'
assert sha(cnf)=='459cfa232e1c5fd55bd065db8dba50699103b612daaaf88b65636b77007687fa'
assert sha(cnf)==sha(R/'milestones/183-critical-floor15/cache/012034-floor15-dense.cnf')
finished=list(range(38))+[i for i in range(38,98) if f'Share187.Shard{i:02d}' in accepted]
assert finished==list(range(len(finished)))
batches=len(finished);clauses=sum(min(128,12424-128*i) for i in finished)
composed='Share187.Compose' in accepted
failures=[]
for p in sorted((H/'logs').glob('*/record.json')):
    j=read(p)
    if j['status']!='PASS':failures.append({'module':j['module'],'reason':j.get('stop_reason'),'exit_code':j['exit_code'],'record':str(p.relative_to(H))})
result=dict(round=187,status='PROGRESS; CONDITIONAL_233_SLACK_CHECKED; CRITICAL_LOCAL_PROOF_INCOMPLETE',
    pause_requested=True,next_round_started=False,timed_phase_start_utc='2026-11-10T15:02:33+00:00',
    closed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),planned_current_modules=len(order),
    accepted_modules=len(accepted),accepted_module_names=accepted,remaining=[n for n in order if n not in accepted],
    theorem_dependency_reports=reports,inherited_round185_modules=98,inherited_round186_modules=len(oldnames),
    concrete_clause_batches_checked=batches,concrete_clause_batches_total=98,clauses_in_complete_batches=clauses,
    initial_database_truth_checked=composed,critical_Lean_refutation_complete=False,actual_snake_floor15_complete=False,
    boundary_slack_sequence_theorems_checked=True,new_233_actual_snake_integration_complete=False,
    contributor_233_independent_rebuild_complete=False,contributor_commit=read(H/'data/contributor-snapshot.json')['commit'],
    maintained_range=[191,235],archived_235_independent_rebuild_pending=True,cnf_sha256=sha(cnf),
    cnf_clauses=12424,proof_variables=5342,interpretation_variables=5906,native_deductions=52489,
    prior_boundary_and_domination_receipts=prior,validated_unique_dependency_files=len(cache),
    resource_snapshot=snap,failures=failures,
    manuscript_review='Current explanation and evidence summary updated; full manuscript-wide review remains pending.')
(H/'data/completion.json').write_text(json.dumps(result,indent=2)+'\n')
(H/'scripts/finish_round.py').write_bytes(Path(__file__).read_bytes())
(H/'scripts/publication.py').write_text((old/'scripts/publication.py').read_text().replace('Round186','Round187'),newline='\n')
(H/'.gitattributes').write_bytes((old/'.gitattributes').read_bytes())
finding=f'{batches}/98 complete clause batches ({clauses}/12,424 clauses) now pass Lean; {len(accepted)} new modules are accepted.'
note='''# Boundary contribution and weaker share requirements

## Checked deduction

Let m count snake edges, T be the total singleton count, sigma_i the nonnegative integer empty-square shares, and L the physical rounding loss. Keep the existing six-step table and its original weights. Put N=m-7. At step n the table weight is 120 b_(n+7)+S_n, where b_i<=alpha_i. Require only S_n<=sigma_(n+3)+...+sigma_(n+7)+q, and let W be the sum of these original weights.

Six omitted internal counts contribute at least 14 and the two endpoints at least 8. Thus the retained count sum is at most T-22. Each physical share occurs in at most five windows. Consequently

    W <= 120(T-22)+5 sum(sigma_i)+q(m-7).

Substitute the exact identity 24T+sum(sigma_i)+840(m+1)+L=221136:

    W+4200m+5L <= 1098840+q(m-7).

This improves the contributor's omitted-count contribution from 14 to 22, gaining 120*8=960 units. The original finite potential and original table weights are retained; only the geometric share requirements are weakened.

The B233 potential has slope 520. Its existing 10-bit representation gives range at most 1023, hence 520(m-7)<=W+1023. With q=4:

    4716m+5L <= 1103475.

At m=234 the left side is at least 1103544, a contradiction by 69. Thus m<=233 under the stated premises. If the sharper range 784 is certified, q=5 gives 4715m+5L<=1103229, excluding 234 by 81.

Both deductions pass Lean for arbitrary natural-valued sequences. They do not yet identify the contributor's complete actual-snake semantics with these sequences. That integration remains a separate task.

## What larger slack requires

With q=5 and range 1023, any m>=234 would force L<=31. Therefore five-point slack suffices when L>=32 in that hypothetical case. Equivalently, five-point requirements may be used generally if four-point requirements can be proved whenever L<=31. These implications also pass Lean.

The earlier actual-snake theorem says an undominated cube vertex contributes at least 96 to L. Consequently the remaining low-loss case is dominating. This provides a geometric restriction for the hybrid argument; it does not establish the stronger local shares in that case.

The scalar pair m=234,W=117017,L=0 satisfies the q=5, range-1023 premises. The pair m=234,W=117256,L=0 satisfies q=6, range-784. These examples are Lean-checked arithmetic limitations, not snake constructions or counterexamples to the geometric statements.

## Finite table consequences

The exact saved table has 23,783 share rows, including 490 rows requiring paid certificates. Reducing every requested level by four, with a floor of zero, makes 31 of these rows follow from nonnegativity or established universal share-16 floors: 17 level-four rows and 14 level-twenty rows. This leaves 459. If the critical 012034 floor fifteen is completed, another 53 rows become covered, leaving 406. With five-point slack the corresponding counts are 459 and 399.

Two more established floors, share twelve for 012310 and for six distinct directions, cover 33 additional paid rows. Their source and object hashes match the earlier integration receipt. Sixteen of these rows already follow at the original level; seventeen need the new slack. Thus the complete census using these six universal floors leaves 426 paid keys, or 373 after the critical floor fifteen is completed (366 with five-point slack). The earlier 459/406/399 figures deliberately use only the four universal share-16 floors already ported into Floors233. See data/floor12-census.json for the added rows and evidence.

These are native table counts. The relaxed lookup wrapper and complete coverage proof have not been checked in Lean, the older full dependency closure was reused rather than rebuilt, and no runtime saving has been measured. The plain/H8 certificate obligations are unchanged.

## Contributor evidence and current limits

The inspected contributor revision is e7b21e0c8704b716115cda60a05e3b4c5d1c059f on research/unconditional-241. Its saved source and Linux log give a conditional 233 chain using the established share floors. The production update reports all 204 automaton shards compiled and all 6,163 new certificate cores generated: 5,673 plain/H8 and 490 share. Full production refutation replay and assembly remain pending. This round inspected and preserved that evidence; it did not independently rebuild that chain locally.

The project interval remains 191--235, with the archived 235 proof's complete independent rebuild pending. There is no new unconditional upper bound, longer construction, or proof of 196.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
paper=r'''\subsection{Reducing the share requirements in the six-step comparison}\label{sec:slack233}
The contributor's six-step comparison now has a checked conditional
implication to $m\le233$, with its production local certificates still
pending. Its saved source and compilation record have been inspected;
an independent rebuild is incomplete. The following deduction weakens
the share premises while preserving the original table and potential.

Assume $m\ge7$. Let $S_n$ be the table's share value at step $n$,
and let $\sigma_i$ denote the physical integer share at path vertex $i$.
Suppose each step satisfies
\[
S_n\le\sigma_{n+3}+\sigma_{n+4}+\sigma_{n+5}
       +\sigma_{n+6}+\sigma_{n+7}+q,
\qquad 0\le n<m-7.
\]
Here $q$ is a nonnegative integer allowance. Write
$W=\sum_{n=0}^{m-8}(120b_{n+7}+S_n)$, with $b_i\le\alpha_i$.
The six omitted internal counts sum to at least fourteen and the two
endpoints contribute at least eight. Each physical share occurs in at
most five windows. Therefore
\[
W\le120(T-22)+5\sum_{i=0}^{m}\sigma_i+q(m-7).
\]
Substitution of the exact physical share identity gives
\begin{equation}\label{eq:slack-budget233}
W+4200m+5L\le1098840+q(m-7).
\end{equation}
The omitted-count contribution improves from fourteen in the contributor's
present accounting to twenty-two, a gain of $120\cdot8=960$.

\begin{proposition}[Four-unit allowance in the share requirements]
Suppose the original potential gives $520(m-7)\le W+1023$ and the
share requirement above holds with $q=4$. Then $m\le233$.
\end{proposition}
\begin{proof}
Combining the potential inequality with~\eqref{eq:slack-budget233} gives
\[
4716m+5L\le1103475.
\]
At $m\ge234$ the left side is at least $1103544$, since $L\ge0$.
The excess is 69. Paths with fewer than seven edges already satisfy
the conclusion.
\end{proof}

A certified potential range of 784 would allow $q=5$ instead:
$4715m+5L\le1103229$, excluding $m\ge234$ by 81. With the existing
range 1023, the five-unit allowance gives
$4715m+5L\le1103468$. Hence a remaining snake of length at least 234
would have $L\le31$. It suffices to establish the four-unit requirements
only in this low-loss case and the five-unit requirements generally.
The earlier domination theorem applies, since $31<96$: every cube vertex
then has a selected neighbour. The required improved shares in this
dominating case remain unproved.

These arithmetic implications pass Lean, including examples showing their
limits: $(m,W,L)=(234,117017,0)$ satisfies the five-unit inequalities with
range 1023, and $(234,117256,0)$ satisfies the six-unit inequalities with
range 784. These are numerical examples, with no claim of geometric
realizability. The new sequence argument still requires integration with
the contributor's actual-snake interpretation.

A native count of the saved share table finds that the four-unit allowance
reduces its 490 paid share obligations to 459 using the four universal
share-sixteen floors already present in the contributor's chain.
The two established universal share-twelve floors cover 33 further rows,
leaving 426. Completion of the critical $012034$ floor fifteen would
reduce this to 373. Five-unit allowance would give 366 with that floor.
These counts have no completed Lean coverage proof and measure certificate
requirements, rather than computation time. The separate count-certificate
requirements remain unchanged. Thus 233 remains conditional.

'''
short=r'''\paragraph{The conditional 233 comparison and weaker share requirements.}
The contributor's six-step argument now supplies a conditional bound 233.
Its saved source and Linux compilation record have been inspected;
the production local certificates and an independent rebuild remain
unfinished. A new deduction reduces the share requirements in that argument.

Keep its original table weights and write their sum as $W$.
There are $m-7$ windows. Suppose each table share value exceeds the physical
five-centre share by at most $q$. The omitted six internal counts and two
endpoints contribute at least $14+8=22$, while every physical share is
counted at most five times. Consequently
\[
W\le120(T-22)+5\sum_i\sigma_{12}(x_i)+q(m-7).
\]
The exact identity in Section 2 then gives
\[
W+4200m+5L\le1098840+q(m-7).
\]
The original potential supplies $520(m-7)\le W+1023$. Setting $q=4$ yields
\[
\boxed{4716m+5L\le1103475\quad\Longrightarrow\quad m\le233.}
\]
Indeed, $m=234$ makes the left side at least $1103544$, exceeding the
right side by 69. This uses the stronger boundary contribution to gain
960 units, permitting weaker local shares without changing the potential.

Five units of allowance would suffice if a smaller potential range of
784 were certified. With range 1023, five units instead force $L\le31$
for any remaining $m\ge234$. The earlier domination theorem then forces
every cube vertex to have a selected neighbour. Thus another sufficient
route is to prove the four-unit requirements in this low-loss case and
the five-unit requirements generally. The stronger low-loss shares are
still unproved. All these numerical implications pass Lean; their
integration with the contributor's actual-snake argument is pending.

In the saved table, four-unit allowance makes 31 of 490 paid share
obligations follow from the four share-sixteen floors. Two established
share-twelve floors cover another 33 rows, leaving 426. Completing the
critical $012034$ floor fifteen would leave 373. These are native table
counts, with the Lean lookup and coverage proof still pending.

'''
proofstatus=f'At the end of round 187, {batches} of 98 complete clause batches ({clauses} of 12,424 clauses) have passed Lean. '
proofstatus+=('The conditional initial-database truth theorem has also passed. ' if composed else 'The initial-database truth theorem remains incomplete. ')
proofstatus+='The full critical contradiction and the actual-snake floor-fifteen theorem remain pending.\n\n'
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name;s=p.read_text(encoding='utf-8');authors=re.findall(r'\\author\{[^\n]+',s);hyper=re.search(r'\\hypersetup\{.*?\n\}',s,re.S)
    assert r'\label{sec:slack233}' not in s
    s=s.replace('Both the endpoint counter and all 72 totalizer conditions are now checked. 38 of 98 concrete clause batches have passed.',
        'At the end of round 186, the endpoint counter, all 72 totalizer conditions, and 38 of 98 concrete clause batches had passed.')
    marker=(r'\section{Remaining requirements for a stronger bound}\label{sec:closure}' if name=='snake9_research.tex' else r'\textbf{6. What is proved, and what remains.}')
    assert marker in s;s=s.replace(marker,proofstatus+(paper if name=='snake9_research.tex' else short)+marker,1)
    if name=='snake9_research.tex':
        s=s.replace('For the current share argument, the sufficient pending local floors are','For the retained seven-step share argument, the sufficient pending local floors are',1)
        s=s.replace('proofs. Thus 234 remains conditional. No new unconditional numerical',
          'proofs. A separate contributor comparison gives conditional 233. We show\nthat the stronger six-count boundary permits a four-unit allowance in\neach of its share requirements; the arithmetic passes Lean, while the\ncomplete actual-snake integration and local certificates remain pending.\nNo new unconditional numerical',1)
        row='Conditional bound 234 &'
        s=s.replace(row,'Conditional bound 233 & Contributor chain and saved Linux evidence inspected; production local certificates remain pending. New boundary accounting permits four units of share allowance, with the actual-snake integration unfinished.\\\\\n'+row,1)
    else:
        s=s.replace('Research state after round 186','Research state after round 187')
        s=s.replace('The argument and these\nlimitations are given in order.','A separate contributor chain gives conditional 233; the new boundary\nargument weakens its local share requirements. Its full certificate\nassembly and the new geometric integration remain pending. The argument\nand these limitations are given in order.')
        s=s.replace('The numerical upper bound 234 remains conditional.','Both the retained bound 234 and the contributor bound 233 remain conditional.')
        s=s.replace('The remaining work is therefore:\n\\begin{enumerate}',
          'The remaining work is therefore:\n\\begin{enumerate}\n\\item Integrate the improved six-count boundary and four-unit share allowance\ninto the contributor comparison. Complete its required local certificates\nand the coverage proof for the relaxed share table.')
        s=s.replace('Round 186 completes the requested continuation.','Round 187 completes the requested continuation.').replace('research records 175--186','research records 175--187')
    assert authors==re.findall(r'\\author\{[^\n]+',s)
    if hyper:assert hyper.group()==re.search(r'\\hypersetup\{.*?\n\}',s,re.S).group()
    p.write_text(s,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes())
status=f'''# Round 187 complete; pause after publication

The user requested completion of this full round and then a pause. Do not start round 188 without a new instruction.

{finding} The complete critical Lean contradiction and actual-snake floor fifteen remain pending. See data/completion.json for the exact accepted modules and the next pending module; partial pieces are listed separately from complete batches.

The main result of this round is a Lean-checked deduction that allows every share requirement in the contributor's conditional 233 comparison to be weakened by four. The stronger omitted-count contribution 22 gains 960 units. Keeping the original table and potential gives 4716m+5L<=1103475, excluding 234 by 69. The actual-snake integration remains pending.

Five-point allowance would suffice with certified range 784. With range 1023 it forces L<=31 for m>=234, so the established domination theorem applies. Proving four-point shares only in that low-loss case, and five-point shares generally, also suffices. This conditional reduction passes Lean; no improved low-loss share theorem has been proved.

The native table census reduces 490 paid share obligations to 426 using six known universal floors, and to 373 if critical floor fifteen is completed (366 with five-point slack). This includes 33 rows covered by the two older share-12 theorems, whose source/object hashes match the saved integration receipt. Sixteen of those 33 already follow at the original level. The narrower census using only four share-16 floors gives 459/406/399. These counts need a Lean lookup/coverage proof and do not measure runtime savings. Plain/H8 obligations are unchanged.

The inspected contributor commit is e7b21e0c8704b716115cda60a05e3b4c5d1c059f on research/unconditional-241. Its conditional 233 source and saved Linux receipts are preserved here. All new native cores are reported generated, but full production Lean replay/glue is pending. That chain was not independently rebuilt locally.

The project range remains 191--235, with the archived 235 proof's full independent rebuild pending. No new unconditional numerical bound, longer construction or proof of 196 is claimed. The retained-profile conditional 234 argument is preserved as a separate route.

Read MATHEMATICAL_NOTE.md for the deduction and limitations, data/share-slack-census.json for the exact rows, and data/current-order.json for proof resumption. The original 12,424-clause input and native 52,489-deduction refutation are unchanged. Do not rerun the solver. The older share-18 replay stays separate at 33,111/145,215 deductions.

Resource limits remain: one sequential Lean worker, 1 GiB free at startup, 256 MiB private memory, 768 MiB free reserve. The failed large cycle piece was replaced by eight-clause pieces; both affected batches pass. All failed attempts and exact snapshots remain saved. No proof worker remains running at closure.

Existing D: manuscripts and E: mirrors are updated with authors and hypersetup preserved. The full manuscript-wide review remains pending. Preserve unrelated changes and accepted proof artifacts.
'''
(H/'README.md').write_text(status,encoding='utf-8',newline='\n')
(R/'handoff/CURRENT_STATUS.md').write_text(status.replace('See data/completion.json','See milestones/187-clause-interpretation/data/completion.json').replace('Read MATHEMATICAL_NOTE.md','Read milestones/187-clause-interpretation/MATHEMATICAL_NOTE.md'),encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('''# Resume only after a new instruction

Round 187 is complete and the user requested a pause. Do not start round 188 automatically.

Read CURRENT_STATUS.md and milestones/187-clause-interpretation/{README.md,MATHEMATICAL_NOTE.md,data/completion.json,data/current-order.json}. Check GitHub before further research. The contributor's conditional 233 chain at e7b21e0c is now stronger than the retained-profile conditional 234 route, but still has production certificate premises.

First integrate the existing actual-snake six-count boundary into that chain. Preserve its original table and potential while allowing four units of slack per physical share window. Reuse BoundarySlack187 and BoundarySlackCases187; their sequence-level deductions pass Lean. A native census using the six proved universal floors gives 426 remaining paid share keys, or 373 after the critical floor-fifteen theorem is completed. Include the two older universal share-12 floors, absent from the contributor's current Floors233 tuple. Inspect data/floor12-census.json: source/object hashes match the earlier receipt; its full imported closure was not rebuilt. Prove the relaxed lookup/coverage wrapper before claiming these key reductions as a complete certificate.

The critical floor-fifteen clause interpretation remains a direct useful dependency. Resume only modules without accepted receipts from current-order.json. Use round187/build, round186/build, round185/build, round147/build in that order. New modules use Share187 while the theorem namespace remains ShareWindow185. Do not introduce a partial Share185 package earlier on the search path. Complete composition, then the compact 52,489-deduction contradiction and actual-snake transfer. The native proof is already complete; do not regenerate it. Preserve all accepted bytes and failure logs.

Alternative within the same route: five-point slack with encoded range 1023 reduces m>=234 to L<=31. The established theorem then gives domination. Four-point share premises in that restricted case and five-point premises generally suffice; the restricted share theorem is unproved. Native range 784 alone is not a checked potential-range certificate.

Keep one heavy worker and the recorded resource limits. Update existing D: sources and E: mirrors, preserving authors and hypersetup. A full manuscript-wide review remains overdue. Do not infer unconditional 233 from arithmetic, native table counts, contributor logs, or completion of one local share proof. The maintained qualified interval remains 191--235.
''',encoding='utf-8',newline='\n')
p=R/'README.md';s=p.read_text(encoding='utf-8');p.write_text(f'''# Current result after round 187

Research pauses after publication. New Lean-checked boundary accounting permits four units of slack in the contributor's conditional 233 share requirements. The complete local certificates and actual-snake integration remain pending. {finding}

No unconditional numerical bound has changed. Read [round 187](milestones/187-clause-interpretation/README.md), [the mathematical deduction](milestones/187-clause-interpretation/MATHEMATICAL_NOTE.md), [the current handoff](handoff/CURRENT_STATUS.md), [the paper](paper/snake9_research.tex), and [the frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+s,encoding='utf-8',newline='\n')
print(json.dumps({k:result[k] for k in ['accepted_modules','planned_current_modules','concrete_clause_batches_checked','clauses_in_complete_batches','initial_database_truth_checked','validated_unique_dependency_files']},indent=2))
