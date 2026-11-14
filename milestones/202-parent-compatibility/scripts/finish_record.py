from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):p.write_bytes(s.replace('\r\n','\n').encode('utf-8'))
def save(p,d):write(p,json.dumps(d,indent=2)+'\n')
def git(*args):return subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0',*args],cwd=R)

modules=['ControlledSymmetry202','ControlledGroup202','WholeSnakeExample202'];proofs=[]
for module in modules:
    receipt=H/'data'/(module+'-audit.json');d=json.loads(receipt.read_bytes())
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    for p,h in d['dependencies'].items():assert sha(p)==h,p
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[pk])==d[hk]
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in d['axioms'])
    proofs.append(dict(module=module,reports=len(d['axioms']),receipt=str(receipt.relative_to(H)),sha256=sha(receipt),seconds=d['seconds']))
census=json.loads((H/'data/component-switches.json').read_bytes())
assert census['script_sha256']==sha(H/'scripts/component_switches.py')
for p,h in census['sources'].items():assert sha(p)==h
assert (H/'data/bank9-input.json').read_bytes()==(R/'work/bank9.json').read_bytes()
assert (H/'data/lower-dimensional-input.json').read_bytes()==(R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json').read_bytes()
q9=[r for r in census['records'] if r['dimension']==9]
assert len(q9)==131
assert sum(sum(r['component_count_distribution'].values()) for r in q9)==9432
assert all(max(map(int,r['component_count_distribution']))<=3 for r in q9)
assert all(o['in_bank'] for r in q9 for c in r['nontrivial'] for o in c['outcomes'])

base='816bbcf557c946227151bc4cee48357f1e7a4d65';head=git('rev-parse','origin/research/unconditional-241').decode().strip()
assert head=='e4b85bb1f447e19a6533fbabe18244b1473c846c','Inspect new contributor changes before publication.'
(H/'logs/contributor-final.diff').write_bytes(git('diff',base+'..'+head))
(H/'logs/contributor-progress.md').write_bytes(git('show',head+':milestones/33-233-lean/CERT-PROGRESS.md'))
contributor=dict(base=base,head=head,diff_sha256=sha(H/'logs/contributor-final.diff'),reported_built=3098,reported_total=3127,
    scope='Read progress and change summary; two remote compiled modules reportedly installed. No independent rebuild or merge; archived235 and conditional233/234 qualifications remain.')
save(H/'data/contributor-final.json',contributor)
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    assert (Path('D:/Codex/2026-10-13/new-chat/outputs')/name).read_bytes()==(R/'paper'/name).read_bytes()
for name in ['main','frontier']:
    d=json.loads((H/'data'/(name+'-compile.json')).read_bytes())
    assert d['isError'] is False
    assert any(json.loads(c['text']).get('kind')=='success' for c in d['content'] if c['type']=='text')

handoff='''# Current state after round 202

The goal is active. The user's explicit resume revoked the round201 pause; no new pause has been requested. Latest steering asks for a more complicated symmetry applicable to the whole snake. Round202 is PROGRESS: an exact whole-snake transformation theorem, checked group deductions and a concrete inequivalent example, a complete native census for this family, and a sharper written parent restriction. No new Q9 witness or global bound was obtained.

Read milestones/202-parent-compatibility/MATHEMATICAL_NOTE.md, logs/independent-proof-review.md and data/completion.json. Choose two coordinates, write (z,u), and let tau_epsilon swap the two square words of parity epsilon while fixing the other diagonal. Define F_f(z,u)=(z,tau_epsilon^(f(z))(u)). The entire selected path is preserved in its order iff f is constant on each component of the base graph induced by fibres containing an active-parity selected vertex. The graph is invariant under the transformation. Every pair relation, including nonedges, is covered.

ControlledSymmetry202 gives10 accepted Lean reports, including a whole induced image path on an arbitrary G square Q2. ControlledGroup202 gives8 reports for composition, complement, rigidity under a constant active selector, compatibility stability and the three-component arithmetic. WholeSnakeExample202 gives3 reports: two complete14-vertex Q5 paths, their image equality, and distance-matrix obstructions to both possible cube-isometry alignments. The component-language reformulation, general cube-isometry equivariance and the bank-closure induction have written proofs. Self-symmetry classification and new parent deductions also remain written, without new Lean assembly. Failed attempts are preserved and accepted sources/objects must stay immutable.

The controlled reflection is an involution of all cube vertices, usually not a cube graph automorphism. It gives isomorphisms between whole embedded snakes. An automorphism of one fixed finite snake is identity or reversal. Within this controlled family a nontrivial self-map agrees on that snake with the ordinary global square reflection, and requires odd vertex count. Do not describe the operation as an additional intrinsic automorphism. Controlled swaps have prior art in Fredkin and Toffoli (1982); novelty is not claimed.

The native census covers all coordinate pairs and both parities, with exact input copies in data/. The saved Q6,Q7,Q8 seeds have connected active graphs in all30,42,56 cases respectively. This family cannot change the saved98-edge parent beyond ordinary isometry. The131 Q9 snakes give9432 cases:9248 connected,144 rank2,40 rank3. Their408 single-component images give111 cube classes, all existing bank classes. There are4 additional Q5 images. With rank<=3, subset complements reduce every combination to identity or a single component up to global reflection. The family is cube-isometry equivariant, with translations potentially interchanging parity. Therefore the union of bank classes is closed under arbitrary iterations with changing coordinate pairs. This conclusion uses native finite premises; no full-bank Lean replay is claimed. Do not repeat this family expecting to escape the bank.

The sharp parent observation concerns the round201195-edge,3-crossing predecessor: exactly one internal deletion lies in each98-edge parent, and their indices have the same parity. If odd, the original parent endpoints have the same base colour. In the saturated C=5 one-addition196 case, the new endpoint attaches at an original parent endpoint. Both exposed neighbours of that parent's omitted vertex are crossing ports; its retained opposite copy joins them into an entire2-edge component in the other face. Hence the other deletion is index3 or95; both deletion indices are odd. This is necessary, with no construction or impossibility result. The review records a further restricted free-involution case giving an induced198-cycle before one deletion; read its assumptions before using it.

Next fundamental direction: enlarge the whole-snake transformation beyond a single square reflection, while keeping a provable all-pair criterion. For an involutive cube isometry h on a larger coordinate block and a Boolean selector on the remaining coordinates, a selector change can alter a cross-fibre matching only when the two selected block words are equal moved words or are h-partners. This suggests a constraint graph on the base fibres recording shared moved h-orbits, rather than assuming every active pair constrains it. This is a proposed generalization requiring a proof and a finite assessment; no claim of new snakes is made. A second concrete proof route is the index3/95 restriction for the saturated parent construction. Preserve the exact one-deletion196 criterion from round201. The13 unresolved round200 repair cases are secondary; latest priority remains fundamental whole-snake proofs.

Contributor branch advanced from816bbcf557c946227151bc4cee48357f1e7a4d65 to e4b85bb1f447e19a6533fbabe18244b1473c846c. Latest inspected progress at03:53 UTC on14 November reports3098/3127 modules built, including2 remotely built modules installed locally. Progress and the full branch diff are archived. No merge or independent rebuild was performed. Archived235 rebuild remains pending;233/234 stay conditional. Future routine fetches should name main and research/unconditional-241 explicitly to avoid repeatedly downloading large temporary xfer branches; the initial round202 full fetch downloaded their transfer pack and finished successfully.

Both existing D:/Codex/2026-10-13/new-chat/outputs manuscripts are edited in place and mirrored in E:/Snake-in-a-box/paper. Preserve all authors and local hypersetup. Both compilation successes and initial stale-project responses are saved separately. Whole-paper review was round200; next remains210. Preserve unrelated .gitignore and milestone50 critical-family.json edits. Keep one heavy worker,1GiB free memory at Lean startup,768MiB reserve,256MiB private per Lean process and60-second limit. No background research job is scheduled by this round.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:write(R/'handoff'/name,handoff)
prefix='''# Current result after round 202

A controlled square reflection now has an exact criterion preserving every edge and nonedge of a whole snake. Three Lean modules pass with 21 dependency reports and a concrete example beyond cube isometry. The native census shows rigidity of the saved 98-edge Q8 parent under this family, and closure of the saved Q9 bank under its arbitrary iterations. A separate written proof restricts one omission in the saturated overlap-five construction to index 3 or 95.

No new Q9 witness or global bound was obtained. The goal remains active. Read [round202](milestones/202-parent-compatibility/README.md), [the argument](milestones/202-parent-compatibility/MATHEMATICAL_NOTE.md), [verification](milestones/202-parent-compatibility/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
p=R/'README.md';assert p.read_text(encoding='utf-8').startswith('# Current result after round 201')
write(p,prefix+p.read_text(encoding='utf-8'))
completion=dict(round=202,status='PROGRESS',previous_turn_classification='PROGRESS: round201 published the crossing/deletion identities and concrete coordinate obstruction.',goal_status='active',
    utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=git('rev-parse','HEAD').decode().strip(),
    new_q9_record=False,new_global_bound=False,accepted_lean_modules=modules,theorem_reports=sum(p['reports'] for p in proofs),proofs=proofs,
    scope='Exact edge-wise whole-set preservation and whole induced image path, group deductions and complete small example are Lean-checked. Component/equivariance/closure and self-symmetry proofs retain the written scope stated in the note.',
    native_census=dict(path='data/component-switches.json',sha256=sha(H/'data/component-switches.json'),q9_cases=9432,q9_component_counts={'1':9248,'2':144,'3':40},q9_single_images=408,q9_image_classes=111,classes_outside_bank=0,full_lean_replay=False),
    written_parent_result='In the C=5 one-addition196 equality case, both deletion indices are odd and at least one is3 or95.',
    contributor=contributor,compiled_documents=['main','frontier'],solver_searches=[],next_full_manuscript_review=210,
    next_action='Continue the active goal with a larger-block involutive whole-snake transformation and an exact global preservation criterion, or develop the saturated parent restriction. Do not repeat the closed two-coordinate family as an escape search.')
save(H/'data/completion.json',completion)
print('SAVED_ROUND202',len(modules),'modules',completion['theorem_reports'],'reports; goal active.')
