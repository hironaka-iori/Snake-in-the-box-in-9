"""Freeze checked research, linked search evidence and the active handoff."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):p.write_text(s.strip()+'\n',encoding='utf-8',newline='\n')
def save(p,x):write(p,json.dumps(x,indent=2))
assert not (H/'data/history-search.lock').exists()
s=json.loads((H/'data/search-summary.json').read_bytes())
assert s['status']=='OPEN'
assert sha(H/'data/case-22/state.json')==s['state_sha256']
proofs=[]
for name,count in [('TwoStep216',5),('Joint216',3),('PathJoint216',1),('LiteralJoint216',2)]:
    p=H/'data'/(name+'-audit.json');d=json.loads(p.read_bytes())
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[pk])==d[hk]
    for path,digest in d['dependencies'].items():assert sha(path)==digest
    assert len(d['axioms'])==count
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in d['axioms'])
    proofs.append({'module':name,'receipt':str(p.relative_to(H)),'sha256':sha(p),'reports':count})
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile.json'),('snake9_research.tex','main-compile.json')]:
    p=D/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
    before=(H/'data'/('before-'+name)).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
    labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
    assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
    result=json.loads((H/'data'/receipt).read_bytes());assert not result.get('isError',False)
    assert any(json.loads(c['text']).get('kind')=='success' for c in result['content'] if c['type']=='text')
    docs[name]={'editor':str(p),'mirror':str(R/'paper'/name),'sha256':sha(p),'compile_receipt':'data/'+receipt,'compile_sha256':sha(H/'data'/receipt)}
save(H/'data/document-verification.json',{'scope':'Exact mirrors, preserved authors/settings, references and saved compilation success; no page-by-page visual audit.','documents':docs})
chain=json.loads((H/'data/chain-audit.json').read_bytes())
assert chain['status']=='PASS_SAVED_TRANSFER_AND_NEW_TRANSITIONS'
assert chain['final']['sha256']==s['state_sha256'] and chain['new_jobs']==s['new_jobs']
assert chain['cumulative']['jobs']==s['jobs'] and chain['cumulative']['nodes']==s['nodes']
frozen={}
for case,folder,jobs,pending,nodes in [('22','215-word-partner-capacity',740,5,4451277),('23','211-subset-capacity',296,11,3721372),('24','209-slice-capacity',150,8,9625900),('9','209-slice-capacity',150,3,8142891)]:
    p=H.parent/folder/'data'/('case-'+case)/'state.json';d=json.loads(p.read_bytes())
    assert d['status']=='OPEN' and d['committed_jobs']==jobs and len(d['frontier'])==pending and d['nodes']==nodes
    frozen[case]={'path':str(p.relative_to(R)),'sha256':sha(p),'jobs':jobs,'pending':pending,'nodes':nodes}
intent=json.loads((H/'data/round-intent.json').read_bytes());t=s['new_operation_totals']
next_step='Continue the retained(0,6) search with the current joint engine using longer bounded jobs, initially 30 seconds, to spend less time reloading and journaling small subtrees. Preserve the same resource limits and exact saved-frontier accounting. Assess completed cases or an actual new parent before adding further propagation. Pair information is demonstrably stricter in the saved comparison, but a controlled speed gain remains unproved. For any further mathematical extension, require an explicit relation or geometric witness beyond the existing root projections.'
completion={'round':216,'status':'PROGRESS','previous_goal_turn':'PROGRESS','started_utc':intent['started_utc'],
    'utc':datetime.now(timezone.utc).isoformat(),'goal_state':'ACTIVE','pause_policy':intent['pause_policy'],
    'email_sent':False,'email_limitation':'No sending connector available.','interval':[191,233],
    'contributor_revision':intent['contributor_at_start'],'contributor_changed':False,
    'independent_233_rebuild':False,'new_q9_record':False,'new_global_bound':False,
    'new_six_coordinate_exclusions':0,'accepted_new_modules':4,'theorem_reports':11,'proofs':proofs,
    'search':s,'frozen_other_states':frozen,'six_coordinate_unresolved':27,
    'review_hashes':{name:sha(H/'logs'/name) for name in ['joint-engine-review.md','joint-chain-review.md','joint-support-direction.md']},
    'chain_audit_sha256':sha(H/'data/chain-audit.json'),'ledger_version':2,'counter_scope':'milestone-local',
    'complete_native_certificate':False,'complete_normalization_certificate':False,
    'software_tests_created_or_run':False,'compile_success':True,'document_verification':'data/document-verification.json','next_step':next_step}
save(H/'data/completion.json',completion)
note=r'''# Round 216: joint pair support and two-step geometry

The hypothesis was that simultaneous compatibility among three successive free-word groups supplies restrictions missed by independent support. The saved analysis finds additional forbidden pairs, and the new native engine retains them during branching. No new parent, longer snake, complete coordinate-case exclusion or global numerical bound is obtained.

## Mathematical argument

Two consecutive cube edges flip either the same coordinate twice or two different coordinates. Their outer words therefore have Hamming distance0 or2. For distinct decoded outer words the distance is2. Lean checks the equal-length Hamming triangle inequality, the two-step conclusions and their connection to the literal reconstructed path. The actual path supplies each consecutive free-word edge. No zero normalization or raw integer bound is needed for the decoded-distance statement. Raw natural-number inequality cannot substitute for distinct decoded words.

For three current domains A,B,C and necessary binary relations R_AB,R_BC,R_AC, retain an allowed pair(a,b) only when there is some c in C with both(b,c) in R_BC and(a,c) in R_AC. Apply the analogous restriction to the other two relations. The actual third value of a fitting complete assignment witnesses all three supports. Hence each restriction preserves the same assignment; repetition follows by induction. Any later assignment in smaller domains also lies in the root domains, so the restriction remains valid for every descendant.

Joint216 checks pair preservation, preservation under subdomain containment, and contradiction from absent triple support. PathJoint216 composes this with the actual successive free edges; domain fitting and a necessary outer relation remain explicit. LiteralJoint216 checks a concrete support distinction. Four new modules pass with eleven dependency reports using only propext, Classical.choice and Quot.sound. The first triangle-inequality attempt failed because simplification discarded useful context; a goal-only simplification repairs it. The failed attempt is retained and is not part of the accepted proof evidence.

## Why the distinction matters

In frozen region20 at groups(6,7,8), the outer words5 and6 are allowed and have distance2. Their only common six-bit neighbours are4 and7. The analyzed middle domain is

\[
\{19,21,22,25,26,28,35,37,38,41,42,44,55,59,61,62\}.
\]

It excludes both common neighbours. Yet5 has available neighbours21,37, and6 has22,38. Both values survive independent support, while their pair has no common middle support. The literal finite checks establish the common-neighbour list and independent-versus-joint support distinction. They do not independently certify the entire saved CSP or its extraction.

The five saved regions reach fixed points under binary and four-family Hall propagation. Adding the static outer distance0-or2 condition deletes no value. Joint projection excludes940 pair occurrences:896 outer occurrences and44 consecutive ones. Installing one projection pass and repeating those baseline rules still removes no individual value. Counts are by region/triple and may repeat a pair. This comparison omits partner-capacity, lexicographic and higher-order nogood rules. It supplies stricter explicit pair information, without a demonstrated speed advantage or a reproduced full native fixed point.

## Native use and proof boundary

The new engine first runs ordinary root propagation. It then computes all three support tables for each consecutive triple before modifying that triple's relations, maintaining both relation orientations. Missing relations mean universal relations. Only pairs within the current root domains are deleted. Up to four sweeps are interleaved with ordinary propagation. Relation tables then remain fixed for the entire descendant search. Every submitted job starts a fresh process with the original input relations; forgetting inferred restrictions between jobs can cause extra work without losing a valid completion.

The source review found no blocking defect under the existing model assumptions. The new operation preserves solutions of arbitrary binary relations; its correctness does not depend on the variable numbers actually being consecutive snake groups. Applying it to snakes still requires every intended path to satisfy the supplied tables, family restrictions, symmetry and other constraints. The native bitmask/list correspondence, arbitrary-input normalization and complete C traversal remain separate proof obligations. Neither this source review nor the generic Lean result certifies a full native exclusion.

## Saved search and evidence structure

The original round 215 state and its740 receipts remain in their published milestone. The new version2 ledger copies only four pinned model files and a source-state snapshot, preserves all five unfinished domain vectors and next_id, and stores explicit hashes of the predecessor state, audit and publication manifest. Its committed_jobs,nodes,seconds and receipts describe only work performed in round 216. Cumulative quantities in search-summary.json add the history_parent baseline. This is a new local ledger contract, not a silent reinterpretation of older files.
'''
note+=f'''
The continuation accepts {s['new_jobs']} local jobs, with outcomes {s['new_statuses']}, {t['nodes']:,} new nodes and {t['seconds']:.3f} reported solver seconds. It records {t['joint_pair_removals']:,} repeated pair removals over {t['joint_sweeps']:,} root projection sweeps. These counts do not establish a controlled speed gain.

The audited final state remains OPEN with {s['pending']} regions. Cumulative totals are {s['jobs']} jobs, {s['nodes']:,} nodes and {s['seconds']:.3f} reported solver seconds. State SHA-256: {s['state_sha256']}. All predecessor state files remain unchanged. Only retained[1,4] is exhausted among 28 six-coordinate choices; 27 remain unresolved.

## Next step and goal state

{next_step}

The recorded interval remains191<=a(9)<=233. Contributor revision b0521e1d and the saved final audit b65d30ca are unchanged; the original233 theorem is unconditional, while independent full rebuilding remains pending. The196 conjecture remains unresolved.

Goal ACTIVE. Continue across rounds under the user's own-work pause condition; contributor work alone cannot trigger a pause. No email was sent because no sending connector is available. Both existing editor manuscripts compile and exactly match their paper mirrors. All three authors and local hyperlink settings are preserved. Last full-paper review210; next scheduled220.
'''
write(H/'MATHEMATICAL_NOTE.md',note)
handoff=f'''# Current state after round 216

Goal ACTIVE. {intent['pause_policy']} No email sent; no sending connector is available.

Read milestones/216-joint-word-support/MATHEMATICAL_NOTE.md and data/completion.json. Four new Lean modules pass with 11 reports: two-step distance geometry and its actual-path consequence; simultaneous pair preservation and descendant containment; actual-path support composition; a concrete missing-common-neighbour example. Domain/relation premises and native interpretation/execution boundaries remain explicit.

The recorded interval remains191<=a(9)<=233. Contributor b0521e1d and saved audit b65d30ca are unchanged. Independent full rebuilding of233 remains pending. No new snake, parent or complete coordinate-case exclusion was obtained.

| Case | Pair | Saved milestone | Cumulative jobs | Pending | Cumulative nodes |
|---|---|---|---:|---:|---:|
|22|[0,6]|216-joint-word-support|{s['jobs']}|{s['pending']}|{s['nodes']:,}|
|23|[0,5]|211-subset-capacity|296|11|3,721,372|
|24|[0,4]|209-slice-capacity|150|8|9,625,900|
|9|[3,4]|209-slice-capacity|150|3|8,142,891|

Case22 state hash: {s['state_sha256']}. IMPORTANT: version2 state counters and receipt paths are local to216. The summary jobs/nodes/seconds are cumulative; new_jobs/local_nodes/local_seconds are local. history_parent links the immutable215 baseline740jobs/4,451,277nodes. Future transfers should take cumulative totals from the checked summary and preserve this explicit provenance, without treating local counters as lifetime totals. All new transitions and 740 predecessor receipt hashes were audited. The original model is unchanged; per-job root relation restrictions are not carried into other jobs.

Next: {next_step}

Only[1,4] is exhausted among 28 six-coordinate choices; 27 remain unresolved. Saved comparison has940 unsupported pair occurrences but no immediate unary deletion, and omits some native rules. Runtime operation counts do not establish speed improvement.

Keep one heavy worker; startup>=1GiBfree, reserve>=768MiB, private<=256MiB, Lean60s with -j1 -s8192,55s startupwait. Preserve failed attempts and assertions. No software tests unless requested. Never restart a live job on an observation timeout. Do not modify frozen216 evidence or accepted proofs. Preserve unrelated .gitignore and milestone50 edits.

Editor originals remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex. Both compile and match paper mirrors. Preserve author order and hypersetup. Last full-paper review210; next220. Publish only the exact scoped manifest.
'''
write(R/'handoff/CURRENT_STATUS.md',handoff);write(R/'handoff/NEXT_AGENT_PROMPT.md',handoff)
header=f'''# Current result after round 216

Joint word-pair support is checked in Lean and retained at each submitted search root. The new continuation examines {t['nodes']:,} nodes and records {t['joint_pair_removals']:,} repeated pair removals. Case[0,6] remains open with {s['pending']} regions. The recorded interval remains191<=a(9)<=233; no numerical bound or new construction is obtained, and the contributor proof's independent full rebuild is pending.

Read [the mathematical argument](milestones/216-joint-word-support/MATHEMATICAL_NOTE.md), [evidence](milestones/216-joint-word-support/data/completion.json), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex). The goal remains active. New search ledgers store local counters and link prior evidence explicitly.

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 216')
write(R/'README.md',header+old)
write(H/'README.md','''# Round 216: joint word support

Read MATHEMATICAL_NOTE.md and data/completion.json. Four Lean modules pass with 11 dependency reports. Saved-domain analysis, native source review and linked-ledger audit retain their stated scope. The model remains open and the goal remains active. Version2 state counters are local; the summary supplies cumulative totals.
''')
print('FROZEN_ROUND216',len(proofs),'modules;11 reports; ACTIVE')
