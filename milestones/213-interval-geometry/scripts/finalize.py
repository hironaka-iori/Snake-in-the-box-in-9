"""Freeze accepted evidence, document verification and the round handoff."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):p.write_text(s.strip()+'\n',encoding='utf-8',newline='\n')
def save(p,x):write(p,json.dumps(x,indent=2))
assert (H/'data/PathSupport213-audit.json').exists()
proofs=[]
for p in sorted((H/'data').glob('*-audit.json')):
    d=json.loads(p.read_bytes())
    if Path(d['source']).parent!=H/'lean':continue
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[pk])==d[hk]
    for q,digest in d['dependencies'].items():assert sha(q)==digest
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in d['axioms'])
    proofs.append({'module':d['module'],'receipt':str(p.relative_to(H)),'sha256':sha(p),'reports':len(d['axioms'])})
documents={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile.json'),('snake9_research.tex','main-compile.json')]:
    p=D/name;mirror=R/'paper'/name;assert p.read_bytes()==mirror.read_bytes()
    before=(H/'data'/('before-'+name)).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
    labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after));assert {x.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for x in g.split(',')}<=bib
    result=json.loads((H/'data'/receipt).read_bytes());assert not result.get('isError',False)
    assert any(json.loads(c['text']).get('kind')=='success' for c in result['content'] if c['type']=='text')
    documents[name]={'editor':str(p),'mirror':str(mirror),'sha256':sha(p),'compile_receipt':'data/'+receipt,'compile_sha256':sha(H/'data'/receipt)}
save(H/'data/document-verification.json',{'scope':'Exact mirrors, preserved authors/settings, references and saved compilation success; no page-by-page visual audit.','documents':documents})
frozen={'22':('212-spare-support',120,11,1051511,'6a2090ba3a2af9561461bf7ff5f6ef133996a25c13dbc32d48f74d29b2aa90a8'),'23':('211-subset-capacity',296,11,3721372,'3b7733ba9ad904608c050ed63199b13a295c56db6d3b1ded909ef13be38d5e7d'),'24':('209-slice-capacity',150,8,9625900,None),'9':('209-slice-capacity',150,3,8142891,None)}
states={}
for key,(folder,jobs,pending,nodes,digest) in frozen.items():
    p=H.parent/folder/'data'/('case-'+key)/'state.json';s=json.loads(p.read_bytes())
    assert s['status']=='OPEN' and s['committed_jobs']==jobs and len(s['frontier'])==pending and s['nodes']==nodes
    if digest:assert sha(p)==digest
    states[key]={'path':str(p.relative_to(R)),'sha256':sha(p),'jobs':jobs,'pending':pending,'nodes':nodes,'status':'OPEN'}
completion={'round':213,'status':'PROGRESS','previous_turn':'PROGRESS','started_utc':'2026-11-14T16:39:27+00:00','utc':datetime.now(timezone.utc).isoformat(),'goal_state':'PAUSE_AFTER_PUBLICATION','pause_basis':'User authorized pausing at a significant result. The completed contributor233 theorem changes the recorded frontier, and this round closes the source-specific geometric support premises.','email_requested_if_possible':True,'email_sent':False,'email_limitation':'No email-sending connector available in this session.','current_interval':[191,233],'upper_bound_evidence':'Completed contributor theorem at b0521e1d with successful saved assembly/axiom audit; independent full rebuild pending.','contributor_branch_merged':False,'independent_233_rebuild':False,'new_q9_record':False,'new_own_global_bound':False,'new_six_coordinate_exclusions':0,'new_search_steps':0,'proofs':proofs,'accepted_new_modules':len(proofs),'theorem_reports':sum(x['reports'] for x in proofs),'concrete_required_pairs':1291,'count_1291_evidence':'Native extraction; Lean checks exact required-pair coverage and all witnesses without a separate numeric-length theorem.','remaining':'Alphabet/domain membership, normalization, literal native masks and traversal; independent full contributor233 rebuild.','frozen_search_states':states,'six_coordinate_unresolved':27,'compile_success':True,'document_verification':'data/document-verification.json','software_tests_created_or_run':False}
save(H/'data/completion.json',completion)
note=r'''
# Round 213: indexed-path geometry and the completed contributor bound 233

The previous round made progress through spare-word support restrictions. This round derives their source-specific geometric premises from the indexed path and updates the numerical frontier from new contributor evidence. No construction search ran; no new snake or six-coordinate exclusion was obtained.

## Contributor result

Revision b0521e1d14fd52c62db4cdeccc356b70a623eb82 contains the completed unconditional theorem a(9)<=233 and the interval theorem with the verified 191-edge witness. The final source supplies both certificate families and the floor results. The successful saved assembly/axiom audit at b65d30ca exits zero and reports only propext, Classical.choice and Quot.sound. For the original window weight W and m>=7,

\[
520(m-7)\le W+1023,\qquad W+4200m\le1099800,
\]

so 4720m<=1104463, whereas 4720*234=1104480. Length 234 is excluded by17; shorter cases are immediate. The recorded interval is now 191<=a(9)<=233. This advance belongs to the contributor chain.

The review inspected the final theorem, relevant composition and saved audit, and saved eleven exact Git blobs. The audit reused 172 of173 chain modules. Nineteen certificates came from cloud builds, floor objects came from an external overlay, generated certificate sources require regeneration, and replay provenance includes preserved timestamps. Independent full rebuilding remains pending. These are verification limitations, rather than premises of the final theorem. The branch was not merged. Separate retained234 and relaxed233 comparisons keep their original unresolved premises and are numerically subsumed. See logs/contributor233-review.md and data/contributor233-review.json.

## Path geometry and concrete support

Write the indexed path as (z_i,u_g(i)), with z_i in the retained square and a constant free word per group. Consecutive identifiers stay equal or increase by one. Representatives of different groups with equal identifier parity cannot be consecutive. If their free words agree, their bases must be opposite, because nonconsecutive full vertices have distance at least two.

Fixing one representative fixes the other group's base and free word. Injectivity permits only one original index in that other group. Three sharing groups would repeat the first full vertex after taking the opposite twice. Lean checks this directly from the indexed-path condition and group-step property.

For retained coordinates [0,6], the literal grouping is checked against all99 source vertices: start at0 and increment exactly when consecutive retained base words agree. The chosen/outside families and partner lists match the frozen model. Every required pair has original-index witnesses with nonopposite bases. There are1291 pairs by native extraction; Lean checks the exact required relation, every witness and full assembly. Nineteen final witness tuples differ from the exploratory first-found tuples in concrete-extraction.json; the current proof consistently uses makeCertificate and its checked witnesses.

ConcreteSupport213 derives distinct chosen values, distinct outside values and partner completeness from an induced Q8 path reconstructed with this grouping. PathSupport213 then composes these results with spare capacity: with a32-entry pool and explicit domain containment, two forced even exceptions or six forced odd exceptions force each remaining outside value into partner support. The same complete assignment survives filtering.

Six-bit decoding of an arbitrary natural value does not establish its range or parity. Alphabet membership, assignment fitting and support-domain containment therefore remain explicit. Complete coordinate normalization, literal native-mask interpretation and traversal certification remain unfinished. The proof is source-specific and supplies no new universal length bound.

## Verification and retained state

Successful source/object/dependency receipts are enumerated in data/completion.json. Large initial checks exceeded the unchanged256MiB private-memory limit. The final calculation uses generic list reasoning, smaller independently checked pieces and exact take/drop assembly. Accepted prefix modules were preserved while later pieces were split further. Failed attempts and source snapshots remain in logs; only successful audit receipts identify accepted modules. Initial draft generators cannot overwrite accepted sources.

No software tests or native search runs were executed. The four frozen states remain pinned: case22 in round212, case23 in round211, cases24/9 in round209. Twenty-seven six-coordinate choices remain unresolved, and196 is still unproved. The manuscripts compile, preserve all three authors and local hypersetup, and match their paper mirrors.

## Pause and resumption

The user authorized a pause at a significant result. The completed233 theorem changes the global frontier, and the current source-specific path/support composition is complete at its stated scope. Publish this round and pause. No email was sent because no email-sending connector was available.

After explicit resumption, useful choices are an independent rebuild plan for233 or further construction work with the checked geometric support rule. The group inequality from round212 is a possible deeper-search improvement, but it excluded none of that round's eleven saved regions. No performance gain or longer Q9 construction is guaranteed. Preserve these proof boundaries in every continuation.
'''
write(H/'MATHEMATICAL_NOTE.md',note)
handoff='''# Current state after round 213

Round213 is PROGRESS. The user authorized pausing at a significant result. Pause after publication: the completed contributor233 theorem changes the global frontier, and the source-specific path/support composition is checked. Resume only after a new instruction. No email was sent because no sending connector is available.

The recorded interval is191<=a(9)<=233. Contributor revision b0521e1d14fd52c62db4cdeccc356b70a623eb82 and audit b65d30ca15441420b8f4538f671e589c2502674f supply the unconditional theorem and successful saved assembly/axiom audit. Independent full rebuilding remains pending; the branch was inspected and snapshotted, not merged. Do not describe the original233 theorem as mathematically conditional. Separate relaxed233/retained234 routes retain their own unresolved premises.

Read milestones/213-interval-geometry/MATHEMATICAL_NOTE.md and data/completion.json. IntervalGeometry213 derives the sharing geometry from an indexed path. The concrete source recurrence and complete1291-pair certificate derive chosen/outside distinctness and partner completeness. ConcreteSupport213 assembles these; PathSupport213 composes the spare-capacity filter under explicit32-entry pool and domain hypotheses. Only successful audit receipts identify accepted modules. Complete normalization, native masks/traversal and alphabet interpretation remain separate.

No search ran in round213. Only[1,4] is exhausted among28 six-coordinate choices;27 remain unresolved.

| Case | Pair | Saved milestone | Jobs | Pending | Nodes |
|---|---|---|---:|---:|---:|
|22|[0,6]|212-spare-support|120|11|1,051,511|
|23|[0,5]|211-subset-capacity|296|11|3,721,372|
|24|[0,4]|209-slice-capacity|150|8|9,625,900|
|9|[3,4]|209-slice-capacity|150|3|8,142,891|

Use each state's own pinned engine and full receipt prefix. Copy into a new milestone before continuation. Missing states must never be silently regenerated. A changed engine needs a justified transfer. The group inequality gave no immediate exclusion of the eleven round212 regions.

Keep one heavy worker; startup>=1GiB free, reserve>=768MiB, private<=256MiB. Lean60s, -j1 -s8192;55s startup wait preserves thresholds. Keep assertions enabled. No software tests unless asked. Preserve accepted sources/objects and failed logs, plus unrelated .gitignore/milestone50 edits.

Editor originals remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, with exact paper mirrors. Both compile in round213. Preserve authors and hypersetup. Last full-paper review210; next scheduled220. Publish only the exact scoped manifest.
'''
write(R/'handoff/CURRENT_STATUS.md',handoff);write(R/'handoff/NEXT_AGENT_PROMPT.md',handoff)
header='''# Current result after round 213

The contributor branch has completed the unconditional bound233, supported by a saved assembly/axiom audit; independent full rebuilding remains pending. The recorded interval is191<=a(9)<=233. The construction proof now derives [0,6] partner restrictions from the actual reconstructed path and composes the spare-capacity filter. No new snake or construction-search exclusion is obtained.

Read [the argument](milestones/213-interval-geometry/MATHEMATICAL_NOTE.md), [accepted proofs](milestones/213-interval-geometry/data/completion.json), [contributor review](milestones/213-interval-geometry/logs/contributor233-review.md), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex). The user authorized pausing at this significant review point.

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 213');write(R/'README.md',header+old)
write(H/'README.md','''# Round 213: indexed-path geometry and contributor233 review

Read MATHEMATICAL_NOTE.md and data/completion.json. Exact contributor snapshots are in data/contributor233/. The manuscripts compile and preserve authors/settings; see data/document-verification.json. Only successful audit receipts identify accepted Lean modules. Failed larger drafts remain as research history. Pause after publication under the user's significant-result instruction; no email was sent.
''')
print('FROZEN_ROUND213',len(proofs),'modules',sum(x['reports'] for x in proofs),'reports')
