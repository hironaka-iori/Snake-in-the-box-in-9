from pathlib import Path
import hashlib,json,gzip,datetime
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
modules=['Floor14Optimum178','Floor14Obstruction178','LossOneSignature178','ActualFloor14Case178','ScalarFeasibility178']
proofs=[];pins={}
for module in modules:
    p=H/'data'/(module+'-audit.json');j=json.loads(p.read_text())
    assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    for path,digest in j['dependencies'].items():
        if path not in pins:assert sha(path)==digest,path;pins[path]=digest
        else:assert pins[path]==digest
    for key,digest_key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
        assert sha(j[key])==j[digest_key]
    assert all(set(x['axioms'])<={'propext','Quot.sound','Classical.choice'} for x in j['axioms'])
    proofs.append({'module':module,'receipt_sha256':sha(p),'reports':len(j['axioms'])})
profiles=[]
for name in ['fixed14','joint14-opt']:
    p=H/'data'/(name+'.json');j=json.loads(p.read_text())
    assert j['status']=='PASS_POTENTIAL' and j['scan']['edges']==4661572 and j['scan']['violations']==0
    archive=H/'data'/j['potential_file'];assert sha(archive)==j['potential_archive_sha256']
    raw=gzip.decompress(archive.read_bytes());assert hashlib.sha256(raw).hexdigest()==j['potential_sha256']
    profiles.append({'profile':name,'receipt_sha256':sha(p),'scaled_mean':j['scaled_mean'],'scaled_range':j['scaled_range'],'sufficient_integer_loss':j['minimum_integer_loss']})
assert json.loads((H/'data/scalar-witnesses.json').read_text())['status']=='PASS_SCALAR_SOURCE_RECONSTRUCTION'
docs={}
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=R/'paper'/name;assert p.read_bytes()==(D/name).read_bytes();docs[str(p.relative_to(R))]=sha(p)
    before=(H/'data'/(name+'.before.txt')).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    if name=='snake9_research.tex':assert before.split('\\begin{document}')[0]==after.split('\\begin{document}')[0]
    assert before.split('\\author{')[1].split('}')[0]==after.split('\\author{')[1].split('}')[0]
record={'round':178,'status':'COMPLETE_CONDITIONAL_OPTIMIZATION','finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'requested_research_started_utc':'2026-11-05T14:57:06+00:00','new_unconditional_bound':False,'maintained_project_interval':[191,235],'upper235_full_independent_rebuild':'pending','profiles':profiles,'lean_modules':proofs,'theorem_dependency_reports':sum(x['reports'] for x in proofs),'dependency_files_rechecked':len(pins),'actual_snake_implication':'PASS_UNDER_EXPLICIT_LOCAL_WINDOW_AND_POTENTIAL_PREMISES','scalar_integer_witness':{'m':235,'L':1,'G':22895,'W':111595},'remaining_case':'m=235 and L in {0,1}; dominating, at most one positive remainder','loss_one_signature':{'selected_neighbours':5,'empty_incident_squares':3,'geometric_pair_bound':'written direct counting; finite arithmetic checked'},'next_local_target':'Prove universal floor14, and stronger floor15 for low loss; rational share16 is a proposed sufficient target, unproved.','remaining_graph_premises':'Inherited count restrictions, reference exclusions, graph-to-snake coverage, complete Lean edge certificate.','share18_replay':[33111,145215],'documents':docs,'pause_requested':True,'next_manuscript_wide_review':186,'scope':'Finite graph optimum and conditional actual-snake reduction; not a solution of the Q9 optimum.'}
(H/'data/completion.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
(H/'data/latex-compile.json').write_text(json.dumps({'compiler':'Codex desktop built-in compiler','main':'success','short':'success','source_sha256':docs,'visual_page_review':False},indent=2)+'\n',encoding='utf-8')
print('Saved completion:',len(proofs),'Lean modules,',record['theorem_dependency_reports'],'reports,',len(pins),'dependency files')
