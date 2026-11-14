"""Collect accepted proofs, complete partition coverage and document receipts."""
from pathlib import Path
import collections,datetime,hashlib,itertools,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def git(*args):return subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0',*args],cwd=R).decode().strip()
proofs=[]
for p in sorted((H/'data').glob('*-audit.json')):
    d=read(p);assert d['status']=='PASS'
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[pk])==d[hk],d[pk]
    assert all(sha(p)==v for p,v in d['dependencies'].items())
    proofs.append(dict(module=d['module'],reports=len(d['axioms']),receipt=p.relative_to(H).as_posix(),sha256=sha(p),seconds=d['seconds']))
assert len(proofs)==5 and sum(p['reports'] for p in proofs)==28
seed=H/'data/lower-dimensional-input.json';covered=set();partitions=[]
for m in range(1,8):
    filename='face-isometries.json' if m==1 else 'slices-2.json' if m==2 else 'slice-images-'+str(m)+'.json'
    script='face_isometries.py' if m==1 else 'slice_census.py' if m==2 else 'slice_image_census.py'
    p=H/'data'/filename;d=read(p)
    assert d['status']=='COMPLETE' and d['source_sha256']==sha(seed) and d['script_sha256']==sha(H/'scripts'/script)
    subsets={(r['coordinate'],) if m==1 else tuple(r['base_coordinates']) for r in d['records']}
    assert subsets==set(itertools.combinations(range(8),m))
    assert all(r['different_images']==0 and (m==1 or (r['status']=='COMPLETE' and r['cube_classes']==1)) for r in d['records'])
    covered.update(subsets)
    partitions.append(dict(base_dimension=m,partitions=len(subsets),record=p.relative_to(H).as_posix(),sha256=sha(p),seconds=d['seconds'],native_only=True))
assert len(covered)==254
cyclic=[]
for filename in ['cyclic-1-q7.json','cyclic-1-q8.json','cyclic-2-q8.json','cyclic-1-bank9.json']:
    p=H/'data'/filename;d=read(p);assert d['status']=='COMPLETE'
    assert d['script_sha256']==sha(H/'scripts/cyclic_census.py')
    assert all(sha(s)==v for s,v in d['source_sha256'].items())
    counts=collections.Counter();hist=collections.Counter()
    for row in d['records']:counts.update(row['counts']);hist.update({int(k):v for k,v in row['component_histogram'].items()})
    assert counts.get('outside_bank',0)==0
    cyclic.append(dict(record=p.relative_to(H).as_posix(),sha256=sha(p),cases=sum(r['cases'] for r in d['records']),counts=dict(counts),preliminary_component_histogram=dict(sorted(hist.items())),changed_image_classes=d['new_classes'],seconds=d['seconds']))
assert cyclic[-1]['cases']==44016 and cyclic[-1]['counts']['nonzero_assignments']==194
documents=[]
for name,stem in [('main','snake9_research'),('frontier','snake9_frontier_explanation')]:
    receipt=H/'logs'/('latex-'+name+'.json');d=read(receipt);assert json.loads(d['content'][0]['text'])['kind']=='success'
    editor=Path('D:/Codex/2026-10-13/new-chat/outputs')/(stem+'.tex');mirror=R/'paper'/(stem+'.tex');assert editor.read_bytes()==mirror.read_bytes()
    documents.append(dict(name=name,editor=str(editor),mirror=str(mirror),sha256=sha(editor),compiler_receipt=receipt.relative_to(H).as_posix(),compiler_receipt_sha256=sha(receipt)))
review_paths=['logs/independent-proof-review.md','logs/slice-coverage-review.md'];reviews={p:sha(H/p) for p in review_paths}
record=dict(round=204,status='PROGRESS',previous_turn_classification='PROGRESS: round203 proved controlled-block preservation, a differentQ7 parent and native all-involution rigidity for the savedQ8 parent.',goal_status_at_record='active',pause_requested_after_publication=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=git('rev-parse','HEAD'),new_q9_record=False,new_global_bound=False,proofs=proofs,accepted_lean_modules=len(proofs),theorem_reports=28,
 scope='Generic arbitrary-slice whole-path criterion, exact relative matching, column rigidity, selected-image transfer and reconstruction, order-three identities and rigidity, two concrete nonzero-phase chords, and a full small example of failed repetition. Native enumeration and recursive coverage are not a complete Lean certificate.',
 all_partition_comparison=dict(partitions=254,inputs_sha256=sha(seed),records=partitions,cube_classes=1,scope='Saved98-edgeQ8 parent only. Complete image enumeration up to global normalization, with pointwise selected-image identification where specified. All maps preserve the chosen base coordinates; no claim about arbitrary reroutings or all98-edge parents.'),
 cyclic_comparisons=cyclic,reviews=reviews,review_scope='Independent written proof and source inspection, no separate census execution.',documents=documents,
 contributor=dict(head=git('rev-parse','origin/research/unconditional-241'),previous='e4b85bb1f447e19a6533fbabe18244b1473c846c',changed=False,reported_built=3098,reported_total=3127,report_utc='2026-11-14T03:53:00Z',scope='Named refs fetched at start and end; unchanged. No merge or independent rebuild. Archived235 rebuild pending;233/234 conditional.'),
 solver_searches=[],next_full_manuscript_review=210,next_action_after_user_resume='Certify the complete native254-partition comparison in Lean. Construction alternatives must change selected-slice embeddings, use differentQ8 parents, or leave this slice-isometry family; higher-order controlled rotations alone are included in the exhausted family.')
(H/'data/completion.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
(H/'data/contributor-state.json').write_text(json.dumps(dict(utc=record['utc'],**record['contributor']),indent=2)+'\n',encoding='utf-8')
print('SAVED',len(proofs),'accepted modules;28 reports;254 complete partitions;both manuscripts compiled and mirrored.')
