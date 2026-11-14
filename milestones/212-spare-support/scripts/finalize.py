"""Freeze the round's mathematical status, evidence and continuation instructions."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):p.write_text(s.strip()+'\n',encoding='utf-8',newline='\n')
def save(p,x):write(p,json.dumps(x,indent=2))
assert not (H/'data/history-search.lock').exists()
state=json.loads((H/'data/case-22/state.json').read_bytes())
assert state['committed_jobs']==120 and len(state['frontier'])==11 and state['status']=='OPEN'
assert sha(H/'data/case-22/state.json')=='6a2090ba3a2af9561461bf7ff5f6ef133996a25c13dbc32d48f74d29b2aa90a8'
proofs=[]
for name in ['SpareSupport212','SupportBridge212','PartnerSubset212']:
    p=H/'data'/f'{name}-audit.json';d=json.loads(p.read_bytes())
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[pk])==d[hk]
    for p0,digest in d['dependencies'].items():assert sha(p0)==digest
    proofs.append({'module':name,'receipt':str(p.relative_to(H)),'sha256':sha(p),'reports':len(d['axioms'])})
assert sum(p['reports'] for p in proofs)==8
totals={k:0 for k in ['nodes','seconds','support_calls','support_removals','support_failures','saturated_budgets']};statuses={}
for path in state['receipts']:
    p=H/path;r=json.loads(p.read_bytes());o=json.loads(p.with_name('stdout.json').read_bytes())
    assert r['status']=='ACCEPTED_TRANSITION' and sha(p.with_name('stdout.json'))==r['stdout_sha256']
    statuses[o['status']]=statuses.get(o['status'],0)+1
    for k in totals:totals[k]+=o[k]
documents={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile.json'),('snake9_research.tex','main-compile.json')]:
    p=D/name;mirror=R/'paper'/name;assert p.read_bytes()==mirror.read_bytes()
    before=(H/'data'/('before-'+name)).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex':
        assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
        labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
        assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
        bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
        assert {x.strip() for group in re.findall(r'\\cite\{([^}]+)\}',after) for x in group.split(',')}<=bib
    result=json.loads((H/'data'/receipt).read_bytes());assert not result.get('isError',False)
    assert any(json.loads(c['text']).get('kind')=='success' for c in result['content'] if c['type']=='text')
    documents[name]={'editor':str(p),'mirror':str(mirror),'sha256':sha(p),'compile_receipt':'data/'+receipt,'compile_sha256':sha(H/'data'/receipt)}
save(H/'data/document-verification.json',{'scope':'Exact source mirrors, unchanged authors and local main-paper hypersetup, labels/citations and saved compilation success; no page-by-page visual audit.','documents':documents})
analysis=json.loads((H/'data/partner-subset-analysis.json').read_bytes())
assert analysis['state_sha256']==sha(H/'data/case-22/state.json') and not analysis['violating_regions']
reports=['support-engine-review.md','support-input-review.md','spare-chain-review.md','final-math-review.md']
completion={'round':212,'status':'PROGRESS','pause_requested':True,'goal_state':'PAUSE_REQUESTED_AFTER_PUBLICATION','started_utc':'2026-11-14T13:47:57+00:00','utc':datetime.now(timezone.utc).isoformat(),'new_q9_record':False,'new_global_bound':False,'new_six_coordinate_exclusions':0,'accepted_lean_modules':3,'theorem_reports':8,'proofs':proofs,'case22':{'status':'OPEN','jobs':120,'pending':11,'nodes':state['nodes'],'seconds':state['seconds'],'state_sha256':sha(H/'data/case-22/state.json')},'new_results':statuses,'new_operation_totals':totals,'six_coordinate_unresolved':27,'terminal_worker_session':8406,'native_stop':'120-job budget; exit 0; no resource stop or witness','review_hashes':{p:sha(H/'logs'/p) for p in reports},'complete_geometric_model_assembly':False,'complete_native_certificate':False,'software_tests_created_or_run':False,'group_rule_implemented':False,'group_rule_saved_regions_violated':0,'compile_success':True,'document_verification':'data/document-verification.json','next_step':'After explicit resume, retain the frozen case and proof boundaries. Complete the geometric-to-model assembly or evaluate partner matching deeper in search; the group rule gives no immediate exclusion of the eleven saved regions.'}
save(H/'data/completion.json',completion)
note=r'''
# Round 212: spare capacity and partner support

The hypothesis was that the unused parity-word allowance can turn the round-211 aggregate count into a sound domain restriction. The deduction is proved, its generic assignment-level composition passes Lean, and a native implementation is active in the retained-coordinate case [0,6]. The case remains open. No new Q9 construction, global bound or completed six-coordinate exclusion is obtained; 196 remains unresolved.

## Argument

Within one parity alphabet of q words, let C be the chosen interval family and O the outside family. Each family requires distinct assigned words. For each outside interval x, its listed partners contain every member of C with which it can share a word. Let P_x be the union of those partners' current domains, and let s=q-|C|.

At most s outside intervals can use words absent from C: the chosen values use |C| words, and outside values are distinct. If D_x and P_x are disjoint, x is necessarily one of these unshared intervals. More than s such forced intervals contradict capacity. If exactly s are forced, every other outside interval must share with a listed partner, so restricting its domain to P_x preserves the same complete assignment. The forced intervals keep their unshared options. Before capacity is reached, this reasoning permits no individual support restriction on another outside interval.

For the saved source and retained pair [0,6], the even family has 30 chosen and 9 outside intervals, with spare allowance 2; the odd family has 26 chosen and 13 outside intervals, with allowance 6. Each family therefore needs at least seven shared words. These are separate parity alphabets.

There is also a group restriction. For J contained in O, let N(J) be the chosen intervals that are listed partners of some member of J and have a current domain intersecting that member's domain. Every shared member of J determines a distinct partner in N(J); at most s members remain unshared. Therefore

\[
|J|\le |N(J)|+s.
\]

The zero-support rejection is its special case N(J) empty. The general group rule can detect competition for a small partner set even when every interval has individual support. It is proved as a generic deduction, but has not been integrated into this round's search engine. Exhaustive examination of all outside subsets in the eleven saved regions finds no violation: the largest partner deficiency is 1 in each parity, below the respective allowances 2 and 6. Thus there is no immediate additional exclusion at this cutoff. This observation makes no claim about deeper search states or speed improvement.

## Checked logic and remaining premises

Three new Lean modules pass with eight reports. SpareSupport212 checks rejection, saturation, supported values and preservation under domain filtering. SupportBridge212 derives the exception-index budget from assigned words, derives missing-support implies exception, and composes the domain rule without assuming its actual exception list. PartnerSubset212 proves the group inequality. Accepted dependencies contain only propext and Quot.sound, with no admitted proof in the accepted results. The first bridge attempt stopped for low free memory; a later attempt exposed a list-membership simplification error, which was repaired. Failed logs and successful source/object receipts are retained separately.

These results retain distinctness, partner completeness, domain fitting and alphabet hypotheses. The square geometry gives a written justification; the complete arbitrary-snake-to-model Lean assembly, literal native masks and complete native traversal certificate remain unfinished. An independently reviewed native implementation is a separate evidence level from these generic Lean deductions.

## Native model and saved search

The fresh complete root uses the unchanged original case-22 model: 78 domains, 2,600 binary relations, 120 excluded source-isometric assignments and 120 residual permutations. The previous nonresumable two-second run contributes no inherited coverage. The input audit verifies the complete original input prefix, both appended support families, all 41,312 required equality exclusions and all original root domains.

The search accepted 120 transitions: 104 exhausted subtrees and 16 limited runs. It examined 1,051,511 nodes in 76.077 reported solver seconds, recording 63,089 support-value removals and 311 support contradictions. These are repeated operations across branches, not distinct globally excluded assignments. All jobs exited normally; the batch ended at its stated budget. Its final eleven regions are preserved. The complete saved chain reconstructs byte for byte under independent review, while full traversal certification remains pending.

The [0,5] state remains frozen in round211, and [0,4] and [3,4] in round209. Only [1,4] is exhausted among the 28 six-coordinate choices, leaving 27 unresolved. The source-specific six-changed-history requirement from earlier four/five-coordinate enumerations is unchanged.

## Publication and handoff

Both existing editor documents are updated and compile successfully, with exact paper mirrors, all three authors and the local main-paper hyperlink settings preserved. The contributor branch remains at c999e9bd, reporting 3125/3127 certificates; no new merge or independent rebuild is claimed. The completed archived 235 theorem retains its saved successful audit, with independent full rebuild pending. The routes to 234 and 233 remain conditional; the verified construction remains 191 edges.

The user requested a pause after this round. Finish the exact scoped publication and pause the goal; resume research only after a new instruction. On resume, the saved case can be continued with its pinned engine. The group inequality should be evaluated as a possible stronger rule without assuming it improves performance. A direct completion of the geometric-to-model proof would reduce a known verification gap. No software tests were created or run.
'''
write(H/'MATHEMATICAL_NOTE.md',note)
handoff=r'''
# Current state after round 212

Round212 is complete as PROGRESS. The user requested a pause after this round. Resume research only after an explicit new instruction. No new Q9 witness, numerical bound or full six-coordinate exclusion was obtained. The proposed value 196 remains unresolved.

Read milestones/212-spare-support/MATHEMATICAL_NOTE.md, data/completion.json and logs/spare-chain-review.md. Three new Lean modules pass with eight reports. The generic argument now derives actual exception counts from distinct assigned words and connects partner-domain support to sound filtering. The group condition |J|<=|N(J)|+s is also checked. Full geometric/model assembly and native traversal certification remain separate.

## Main deduction

For retained [0,6], at most two even outside intervals and six odd outside intervals may use words absent from the chosen family. An interval with no supported partner consumes one allowance. More than the allowance is impossible. At equality, all other outside domains may be intersected with their partner-domain unions. The implemented engine applies these rules only; it does not require every parity word to occur.

The broader partner-subset inequality is unimplemented. All subsets in the eleven saved regions satisfy it, with maximum deficiency 1 in both parities. This gives no immediate new pruning at the cutoff and no speed claim.

## Frozen states

| Case | Retained pair | Location | Jobs | Pending | Nodes | Status |
|---|---|---|---:|---:|---:|---|
|22|[0,6]|milestones/212-spare-support/data/case-22|120|11|1,051,511|OPEN|
|23|[0,5]|milestones/211-subset-capacity/data/case-23|296|11|3,721,372|OPEN|
|24|[0,4]|milestones/209-slice-capacity/data/case-24|150|8|9,625,900|OPEN|
|9|[3,4]|milestones/209-slice-capacity/data/case-9|150|3|8,142,891|OPEN|

Case22 starts at the complete original root; no old limited-run coverage is inherited. All120 transitions reconstruct exactly. There are104 exhausted subtrees and16 limited results; the final state hash is6a2090ba3a2af9561461bf7ff5f6ef133996a25c13dbc32d48f74d29b2aa90a8. Worker session8406 is terminal, exit0. The120-job budget was reached; no resource stop or witness occurred. Only [1,4] is excluded among28 six-coordinate choices, leaving27 unresolved. The other23 choices retain only their initial limited runs.

## Resume without altering evidence

For [0,6], copy the complete case22 directory, scripts/spare_continue.py, spare_solver.c, history_model.py, native_resources.py, build/spare_solver.exe and both source/census JSON files into a new milestone with identical relative paths. Preserve the complete receipt prefix and engine/model pins. The runner refuses a missing state. A changed engine needs a justified transfer; do not overwrite accepted proof sources, objects or receipts. Other retained pairs use their own earlier engines and states.

One coordinator owns one heavy worker. Keep startup free memory>=1GiB, reserve>=768MiB, private usage<=256MiB; Lean uses60s, -j1 -s8192. The55s startup wait never lowers thresholds. Keep Python assertions enabled. Per-job STOP is not whole-batch cancellation. Full power-loss durability is unproved. Do not create or run software tests unless asked.

The verified construction is191 edges. The completed archived235 theorem has a successful saved audit; its full independent rebuild remains pending.233/234 remain conditional. Contributor revision c999e9bd reports3125/3127 built, with S012301A35344 and T012304A35346K47 pending. No merge or independent rebuild was performed.

Editor originals: D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, exactly mirrored under paper/. Both compile successfully in round212. Preserve author order and local hypersetup. Last full-paper review210; next scheduled220. Preserve unrelated .gitignore, milestone50 critical-family.json and other pre-existing files. Publish only the exact scoped manifest.
'''
write(R/'handoff/CURRENT_STATUS.md',handoff);write(R/'handoff/NEXT_AGENT_PROMPT.md',handoff)
heading='''# Current result after round 212

Spare-word capacity now gives a proved partner-support restriction for the whole-coordinate history model. Three new Lean modules pass with eight reports, including the group inequality |J|<=|N(J)|+s. The implemented rule restricts sharing only after the spare allowance is exhausted.

The [0,6] search remains open after120 saved transitions and1,051,511 nodes, with11 pending regions. No new Q9 witness or global bound is obtained. The user requested a pause after this round; resume only on a new instruction.

Read [the argument](milestones/212-spare-support/MATHEMATICAL_NOTE.md), [proofs and search cutoff](milestones/212-spare-support/data/completion.json), [saved-chain audit](milestones/212-spare-support/logs/spare-chain-review.md), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 212')
write(R/'README.md',heading+old)
write(H/'README.md','''# Round 212: spare capacity and partner support

Read MATHEMATICAL_NOTE.md for the proof, limits and current frontier; data/completion.json records the accepted Lean checks and frozen search. The model remains open. The user requested a pause after this round.

Both manuscript sources compile successfully and match their repository mirrors. See data/document-verification.json. Independent source, input, mathematics and chain reviews are retained in logs/.
''')
print('FROZEN_ROUND212',len(proofs),'modules',sum(p['reports'] for p in proofs),'reports; documents verified')
