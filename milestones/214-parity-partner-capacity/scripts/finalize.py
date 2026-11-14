"""Freeze round214 evidence, mathematical conclusions and active handoff."""
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
assert s['status']=='OPEN' and s['new_jobs']==120 and s['pending']==13
assert sha(H/'data/case-22/state.json')==s['state_sha256']
proofs=[]
for name in ['WordParity214','ConcreteParity214','PathParity214','TightPartner214','PathTight214']:
    p=H/'data'/(name+'-audit.json');d=json.loads(p.read_bytes())
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[pk])==d[hk]
    for path,h in d['dependencies'].items():assert sha(path)==h
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in d['axioms'])
    proofs.append({'module':name,'receipt':str(p.relative_to(H)),'sha256':sha(p),'reports':len(d['axioms'])})
assert sum(p['reports'] for p in proofs)==13
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
reviews=['tight-engine-review.md','tight-chain-review.md']
assert all((H/'logs'/name).exists() for name in reviews)
partner=json.loads((H/'data/partner-subset-analysis.json').read_bytes())
words=json.loads((H/'data/word-capacity-analysis.json').read_bytes())
assert partner['state_sha256']==words['state_sha256']==s['state_sha256']
assert not partner['violating_regions'] and not words['deficient_regions']
frozen={}
for key,folder,jobs,pending,nodes in [('22-old','212-spare-support',120,11,1051511),('23','211-subset-capacity',296,11,3721372),('24','209-slice-capacity',150,8,9625900),('9','209-slice-capacity',150,3,8142891)]:
    case=key.split('-')[0];p=H.parent/folder/'data'/('case-'+case)/'state.json';d=json.loads(p.read_bytes())
    assert d['status']=='OPEN' and d['committed_jobs']==jobs and len(d['frontier'])==pending and d['nodes']==nodes
    frozen[key]={'path':str(p.relative_to(R)),'sha256':sha(p),'jobs':jobs,'pending':pending,'nodes':nodes}
completion={'round':214,'status':'PROGRESS','previous_goal_turn':'PROGRESS','started_utc':'2026-11-14T17:05:49+00:00','utc':datetime.now(timezone.utc).isoformat(),'goal_state':'ACTIVE','pause_policy':'Continue across rounds. Only substantial progress or prolonged lack of progress in the user and this agent work can trigger the authorized pause; contributor work alone cannot.','email_sent':False,'email_limitation':'No sending connector available.','interval':[191,233],'contributor_revision':'b0521e1d14fd52c62db4cdeccc356b70a623eb82','contributor_changed':False,'independent_233_rebuild':False,'new_q9_record':False,'new_global_bound':False,'new_six_coordinate_exclusions':0,'proofs':proofs,'accepted_new_modules':5,'theorem_reports':13,'search':s,'frozen_other_states':frozen,'six_coordinate_unresolved':27,'review_hashes':{name:sha(H/'logs'/name) for name in reviews},'chain_audit_sha256':sha(H/'data/chain-audit.json'),'complete_native_certificate':False,'complete_normalization_certificate':False,'software_tests_created_or_run':False,'compile_success':True,'document_verification':'data/document-verification.json','next_step':'Combine distinct-word subset propagation with the new partner-subset rule, using actual-label capacity. Snapshot analysis finds 72 candidate removals in seven regions, but no deficient family and no established speed gain.'}
save(H/'data/completion.json',completion)
note=r'''
# Round 214: parity alphabets and tight partner capacity

The hypothesis was that competition for partners can force restrictions even when every outside interval has individual support. The finite counting deduction is proved, its connection to the normalized source-specific path passes Lean, and a separate native continuation uses it. The case remains open. The numerical interval remains 191<=a(9)<=233, with the contributor233 proof and independent-full-rebuild qualification recorded in round213. No new snake, numerical bound or complete coordinate-case exclusion was obtained.

## Argument

For one parity, C is the chosen family and O the outside family. Assigned words are distinct within each family and belong to a pool of q words. Write s=q-|C|. For J contained in O, N contains every chosen partner that can share a current-domain word with a member of J. The established necessary inequality is

\[
|J|\le |N|+s.
\]

If equality holds, every outside interval beyond J must share with a chosen interval outside N. To prove this, let E consist of outside intervals using words absent from C. The exception budget gives |E|<=s. Every assigned word on J appears among the values on N or E, so

\[
|J|\le |N|+|E|\le |N|+s=|J|.
\]

Equality exhausts those available words. Distinctness within O prevents an outside interval beyond J from using any of them. It cannot be exceptional or share with N. Its actual chosen partner therefore lies outside N, and the partner's fitted domain supplies the retained value. This proves preservation of the same complete assignment under the support restriction.

For a strict example, take a four-word pool {0,1,2,3}, chosen values fixed to0,1,2, and outside x,y each with domain {0,3} and only the chosen0 as partner. With one spare word, {x,y} is tight. Another outside variable z with domain {0,1,2,3} must use1 or2. Every outside variable has individual partner support initially, so the earlier count of individually unsupported intervals alone gives no deduction. This example concerns the finite capacity model; no claim is made that it is itself a full snake instance.

## Connection to the reconstructed path

The literal 99-index source determines77 boundaries between successive free-word groups. At each boundary the retained base is unchanged; the induced-path condition forces Hamming distance one between successive free words. A general Boolean-word lemma proves that such an edge flips parity. Starting the free word at zero gives weight(u_g) congruent to g modulo2 by induction.

The even and odd six-bit pools each have32 words. Lean checks their lengths and the two literal parity masks, then derives actual membership for bounded raw values below64. The bound is essential: decoding six bits of a larger natural number does not determine its actual integer range. Normalization at zero and the range premise are explicit.

Combining this with round213's geometric distinctness and partner completeness gives the tight filters directly from the actual normalized reconstructed path. The even family has30 chosen variables and spare allowance2; the odd family has26 and allowance6. Current-domain fitting, a duplicate-free subset of outside values, candidate coverage, tight cardinality and support containment remain explicit. Complete normalization from arbitrary equivalent inputs, literal native-domain interpretation and traversal certification are unfinished.

Five new modules pass with13 dependency reports. The accepted dependencies use only propext, Classical.choice and Quot.sound. Two early concrete checks stopped for low free memory. Removing an unnecessary large import and keeping a definitionally identical six-bit decoder reduced the input size; the unchanged resource limits were then met. A separate proof attempt exposed two simplification errors; the repaired proof passes. Failed attempts are retained, and only successful audit receipts identify accepted proofs.

## Native continuation

The augmented candidate graph places the chosen partners and s universal auxiliary slots on one side, and outside intervals on the other. Matching is used to discover subsets. A matching failure rejects only after directly checking |J|>|N|+s. Alternating reachability discovers tight subsets, whose actual neighbor cardinality is checked before filtering. Success of this graph matching is never treated as a valid word assignment. Previously computed neighbor sets remain safe during sequential deletions because they overestimate the remaining support.

The transfer preserves726 prior files and all eleven unfinished domain vectors, changing only the engine pins and adding its transfer record. The independent source review found no defect under the saved geometric family assumptions. The120 new jobs ended normally:105 subtrees exhausted,15 limited runs,749,506 nodes and49.130 reported solver seconds. The new partner rule recorded3,054 value removals and120 contradiction returns. These are repeated operations across branches; they establish neither a number of distinct global exclusions nor a speed improvement.

The independently audited saved chain ends OPEN at240 total jobs,13 pending regions and1,801,017 cumulative nodes. Its final state hash is eb74f9a59a537ee1ac0a7bd9bd3e8dd283c0ca6d5172cc648b6d5aaa6cb6c027. The earlier round212 state is unchanged. Cases23,24 and9 remain at their previous states. Only retained[1,4] is exhausted among the28 six-coordinate choices;27 remain unresolved. The known191-edge construction and the unresolved196 conjecture are unchanged.

## What to pursue next

Every outside subset in the13 saved regions satisfies the partner inequality; the maximum partner deficiency is1 in both parities, below allowances2 and6. Thus simply repeating the same snapshot count gives no immediate exclusion.

The partner graph ignores competition for the actual word labels. A separate finite-domain analysis finds72 candidate word removals across seven saved regions through tight distinct-word subsets, with no deficient family. Some may follow from existing binary propagation; the analysis does not modify a state or establish a performance gain. The useful next implementation is distinct-word subset propagation for both chosen and outside families, combined with the new partner rule. The generic subset-capacity proof from round211 can be reused. Do not assume that candidate matching supplies consistent labels or a new Q9 snake.

The goal remains ACTIVE. The user clarified that contributor work alone must never trigger a pause. Continue across rounds; a pause may follow a substantial result or prolonged lack of progress in the user's and this agent's own work. No email was sent because no sending connector is available. Both existing LaTeX sources compile and preserve author order and local hyperlink settings, with exact paper mirrors. Last full-paper review210; next scheduled220.
'''
write(H/'MATHEMATICAL_NOTE.md',note)
handoff='''# Current state after round 214

Goal ACTIVE. Continue across rounds. A pause may follow a substantial result or prolonged lack of progress in the user's and this agent's own work. Contributor work alone must never trigger a pause. No email was sent: no email-sending connector is available.

Read milestones/214-parity-partner-capacity/MATHEMATICAL_NOTE.md and data/completion.json. Five new Lean modules pass with13 dependency reports. Tight partner capacity now yields support restriction from the normalized actual path, with the32-word parity pools derived. Domain fitting, subset distinctness, candidate coverage, support containment, arbitrary-input normalization and native interpretation/traversal boundaries remain explicit.

The recorded interval remains191<=a(9)<=233. Contributor b0521e1d and saved audit b65d30ca are unchanged. The original233 theorem is unconditional; independent full rebuilding remains pending. No new snake or coordinate-case exclusion was obtained.

| Case | Pair | Saved milestone | Jobs | Pending | Nodes |
|---|---|---|---:|---:|---:|
|22|[0,6]|214-parity-partner-capacity|240|13|1,801,017|
|23|[0,5]|211-subset-capacity|296|11|3,721,372|
|24|[0,4]|209-slice-capacity|150|8|9,625,900|
|9|[3,4]|209-slice-capacity|150|3|8,142,891|

Case22 hash: eb74f9a59a537ee1ac0a7bd9bd3e8dd283c0ca6d5172cc648b6d5aaa6cb6c027. Its tight_solver engine and complete copied receipt prefix are pinned. The new120 transitions and transferred726 files have an independent saved-record audit. Native source review and generic Lean proofs do not certify complete traversal. Only[1,4] is exhausted among28 six-coordinate choices;27 remain unresolved.

Next: integrate distinct-word subset propagation for both C and O with the new partner-subset rule. Word-label competition is lost in the candidate partner graph. Snapshot data/word-capacity-analysis.json gives72 candidate removals across seven regions, with no deficient family; some removals may follow from existing binary propagation. No speed benefit is established. The necessary partner inequality alone excludes none of the thirteen final regions. Reuse round211's generic subset theorem and round213/214 path geometry/parity rather than reproving them.

Copy evidence into a new milestone before continuation; never modify the frozen214 state or accepted proofs. Verify the explicit transfer and exact model/engine pins. Missing state files must not be regenerated silently. Keep one heavy worker; startup>=1GiB free, reserve>=768MiB, private<=256MiB, Lean60s with -j1 -s8192,55s startup wait. Keep assertions enabled and preserve failed attempts. No software tests unless requested. Preserve unrelated .gitignore and milestone50 edits.

The editor originals remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, with exact paper mirrors and successful round214 compilation. Preserve all three authors and hypersetup. Last full-paper review210; next scheduled220. Publish only the exact scoped manifest.
'''
write(R/'handoff/CURRENT_STATUS.md',handoff);write(R/'handoff/NEXT_AGENT_PROMPT.md',handoff)
header='''# Current result after round 214

The normalized reconstructed path now supplies the32-word parity alphabets, and a tight partner-subset theorem gives a stronger assignment-preserving restriction. The native continuation records3,054 value removals by the added rule and749,506 new nodes, while case[0,6] remains open with13 regions. No new snake, numerical bound or complete coordinate-case exclusion is obtained. The recorded interval remains191<=a(9)<=233, with the contributor proof's independent full rebuild pending.

Read [the mathematical argument](milestones/214-parity-partner-capacity/MATHEMATICAL_NOTE.md), [evidence](milestones/214-parity-partner-capacity/data/completion.json), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex). The goal remains active under the clarified pause instruction.

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 214')
write(R/'README.md',header+old)
write(H/'README.md','''# Round 214: parity alphabets and tight partner capacity

Read MATHEMATICAL_NOTE.md and data/completion.json. Lean receipts identify five accepted modules; native source and saved-chain reviews are in logs/. The native case remains open and no global bound changes. Both manuscripts compile. The goal remains active; contributor work alone is not a pause trigger.
''')
print('FROZEN_ROUND214',len(proofs),'modules',sum(p['reports'] for p in proofs),'reports; ACTIVE')
