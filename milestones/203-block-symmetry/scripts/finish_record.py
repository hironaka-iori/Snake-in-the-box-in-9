"""Collect the completed round's proof receipts and documentary evidence."""
from pathlib import Path
import collections, datetime, hashlib, json, subprocess
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def git(*args):
    return subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0',*args],cwd=R).decode().strip()
proofs=[]
for p in sorted((H/'data').glob('*-audit.json')):
    d=read(p); assert d['status']=='PASS'
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
        assert sha(d[pk])==d[hk],d[pk]
    assert all(sha(p)==v for p,v in d['dependencies'].items())
    proofs.append(dict(module=d['module'],reports=len(d['axioms']),receipt=p.relative_to(H).as_posix(),sha256=sha(p),seconds=d['seconds']))
assert len(proofs)==56 and sum(p['reports'] for p in proofs)==71
documents=[]
for name,stem in [('main','snake9_research'),('frontier','snake9_frontier_explanation')]:
    receipt=H/'logs'/('latex-'+name+'.json'); d=read(receipt)
    status=json.loads(d['content'][0]['text']); assert status['kind']=='success'
    editor=Path('D:/Codex/2026-10-13/new-chat/outputs')/(stem+'.tex'); mirror=R/'paper'/(stem+'.tex')
    assert editor.read_bytes()==mirror.read_bytes()
    documents.append(dict(name=name,editor=str(editor),mirror=str(mirror),sha256=sha(editor),compiler_receipt=receipt.relative_to(H).as_posix(),compiler_receipt_sha256=sha(receipt)))
bank=read(H/'data/bank-block-census.json'); hist=collections.Counter()
for row in bank['records']:
    hist.update({int(k):v for k,v in row['distribution'].items()})
assert len(bank['records'])==131 and sum(hist.values())==198072
assert all(o['in_bank'] for row in bank['records'] for case in row['nontrivial'] for o in case['outcomes'])
inputs={n:sha(H/'data'/n) for n in ['parent-block-census.json','bank-block-census.json','three-pair-census.json','parent-placement.json']}
record=dict(round=203,status='PROGRESS',previous_turn_classification='PROGRESS: round202 published controlled square reflection, whole-path criterion, checked example and native closure census.',goal_status='active',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=git('rev-parse','HEAD'),new_q9_record=False,new_global_bound=False,accepted_lean_modules=[p['module'] for p in proofs],theorem_reports=71,proofs=proofs,
 scope='Generic all-pair preservation, induced image path, orbit invariance, composition, selected-fixed-word rigidity, matching and conjugacy identities; complete concrete 51-by-51 pair statement, vertex bounds, image equality and endpoint distances. Component language, classification, equivariance, closure and full geometric growth interpretation retain written proof scope. Native censuses are not a full Lean replay.',
 native_census=dict(input_sha256=inputs,q9_cases=198072,q9_component_counts=dict(sorted(hist.items())),q9_nontrivial_images=bank['total_images'],classes_outside_bank=0,q8_one_pair_cases_from_round202=56,q8_two_pair_cases=840,q8_three_pair_cases=3360,q8_all_block_involutions_rigid=True,q8_scope='Saved98-edge parent only; generic proofs plus written classification and native census premises.',q9_three_four_pairs_examined=False,placement_scope='Both original/new and new/new:645120 relative isometries each,minimum overlap2,maximum92separated vertices after independent contiguous trimming.'),
 contributor=dict(head=git('rev-parse','origin/research/unconditional-241'),previous='e4b85bb1f447e19a6533fbabe18244b1473c846c',changed=False,reported_built=3098,reported_total=3127,report_utc='2026-11-14T03:53:00Z',scope='Named refs fetched; branch unchanged from round202. No independent rebuild or merge. Archived235 rebuild pending;233/234 conditional.'),
 documents=documents,solver_searches=[],next_full_manuscript_review=210,next_action='Investigate higher-order controlled block isometries with exact whole-snake compatibility; savedQ8 parent is rigid under all involutive-block choices. Q9three/four-pair cases and the earlierindex3/95necessaryconstruction remain unresolved.')
(H/'data/completion.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
(H/'data/contributor-state.json').write_text(json.dumps(dict(utc=record['utc'],**record['contributor']),indent=2)+'\n',encoding='utf-8')
print('SAVED',len(proofs),'accepted modules;',record['theorem_reports'],'reports;',sum(hist.values()),'Q9 cases; both compiled mirrors identical.')
