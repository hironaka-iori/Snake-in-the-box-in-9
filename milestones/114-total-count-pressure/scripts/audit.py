"""Check the selected proof evidence, helper receipts and frozen graph experiments."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={}
def pin(p):pins[p.relative_to(ROOT).as_posix()]=sha(p)
modules=[];audits=[]
for name,folder,status,count in [('TotalGeometry114','build-total-geometry','PASS_TOTAL_GEOMETRY',1),
                                ('Comparison114','build','PASS_COMPARISON_ARITHMETIC',3)]:
    p=HERE/'data'/(name+'-audit.json');d=read(p);pin(p)
    assert d['status']==status and d['exit_code']==0 and not d['timeout']
    src=HERE/'lean'/(name+'.lean');assert sha(src)==d['source_sha256']==sha(HERE/d['source_snapshot'])
    assert sha(HERE/folder/(name+'.olean'))==d['olean_sha256']
    assert sha(HERE/d['log'])==d['log_sha256'] and sha(HERE/d['checker_snapshot'])==d['checker_sha256']
    for p,digest in d['dependencies'].items():assert sha(Path(p))==digest,p
    text=src.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
    assert not re.search(r'^\s*(def|abbrev|structure|inductive)\b',text,re.M)
    if name=='TotalGeometry114':assert '(hlocal :' in text
    assert len(d['theorem_audits'])==count==text.count('#print axioms')
    for t in d['theorem_audits']:
        assert set(t['axioms'])<={'propext','Classical.choice','Quot.sound'};audits.append(t)
    pin(src);pin(HERE/d['log']);modules.append(dict(module=name,receipt_sha256=sha(HERE/'data'/(name+'-audit.json'))))

cert=read(HERE/'data/012310-total18-certificate.json');solver=read(HERE/'data/extracted-core-scratch-solver.json')
assert cert['status']=='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING' and solver['status']=='UNSAT_LRAT_UNCHECKED'
assert (cert['core_clauses'],cert['lemmas'],cert['hints'])==(5206,358464,22088504)
assert len(cert['core_ids'])==len(set(cert['core_ids']))==5206
assert sha(HERE/'work/012310-total18/full.cnf')==cert['cnf_sha256']
assert sha(HERE/'work/012310-total18/full.trim.lrat')==cert['lrat_sha256']
assert sha(HERE/'work/extracted-core-scratch/core.trim.lrat')==cert['local_trim_sha256']
assert sha(HERE/solver['raw'])==solver['raw_sha256']
assert sha(HERE/'scripts/replay_core.py')==cert['script_sha256']
assert sha(HERE/'data/extracted-core-scratch-solver.json')==cert['solver_record_sha256']
assert sha(HERE/'data/probes/012310-total18.json')==cert['probe_sha256']
old=HERE/'work/extracted-core/core.raw.lrat';new=HERE/solver['raw'];remaining=old.stat().st_size;h=hashlib.sha256()
with new.open('rb') as f:
    while remaining:
        block=f.read(min(remaining,1024*1024));assert block;h.update(block);remaining-=len(block)
assert h.hexdigest()==sha(old)
for name in ['data/012310-total18-certificate.json','data/extracted-core-scratch-solver.json','scripts/replay_core.py',
             'data/native-core-audit.json','audit/native-core-review.md','data/cycle-audit.json','audit/cycle-review.md',
             'data/pooled-trim.json','data/pooled-cuts-solver.json','data/cycle-cut-pool-extended.json']:
    pin(HERE/name)

pool=read(HERE/'data/pooled-trim.json');assert pool['hints']==29534822 and not pool['fewer_hints']
assert sha(HERE/pool['trim'])==pool['trim_sha256']
cycles=read(HERE/'data/cycle-audit.json')
for label,edgecount,mean,rangevalue in [('total19',4865603,'2424/5','2881/5'),('total20-hypothesis',4859836,'2424/5','565')]:
    p=HERE/'data'/label/'results.json';d=read(p);pin(p)
    assert d['edges']==edgecount
    assert [(x['mean'],x['range'],x['comparison_integer_bound']) for x in d['profiles']]==[(mean,rangevalue,235),('496','602',234)]
    for name,digest in d['source_files_sha256'].items():assert sha(ROOT/name)==digest,name
    assert all(x['all_edge_inequalities_checked'] for x in d['profiles'])
    for x in d['profiles']:assert all(e['bonus']==0 for e in x['cycle'])
for name,status,cuts in [('012310-total18','UNSAT_UNCERTIFIED',8),('012310-total19','UNKNOWN',11)]:
    p=HERE/'data/probes'/(name+'.json');d=read(p);pin(p)
    assert d['status']==status and len(d['cycle_cuts'])==cuts
    assert (d['literal_occurrences'],d['distinct_literals'])==(105,84)

out=dict(status='PASS_NATIVE_TOTAL_CERTIFICATE_CONDITIONAL_TRANSFER_AND_GRAPH_COMPARISONS',modules=modules,
    theorem_audits=audits,native_selected_certificate=dict(core_clauses=5206,lemmas=358464,hints=22088504,
        independent_replay_core_and_original=True,concrete_lean_replay=False),
    geometric_transfer_has_explicit_local_premise=True,new_mathematical_definitions=0,new_global_bound=False,
    fixed_family_coefficient_ceilings=['2424/5','496'],integer_comparisons=[235,234],
    proof_prefix_match_bytes=old.stat().st_size,unselected_pooled_hints=pool['hints'],
    source_files_sha256=pins,script_sha256=sha(Path(__file__)),
    scope='The selected native contradiction was independently replayed in both identifier systems. This audit verifies its frozen bytes and successful helper receipts; it does not repeat the large replay. Complete concrete Lean certification and global integration remain pending.')
target=HERE/'data/proof-summary.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],'Lean modules',len(modules),'axiom reports',len(audits),flush=True)
