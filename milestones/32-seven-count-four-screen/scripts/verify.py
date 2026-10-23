"""Verify the finite coverage audit and the saved experimental evidence."""
import hashlib,importlib.util,itertools,json
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('prior',ROOT/'milestones/28-direct-share-certificates/scripts/verify.py')
prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
def read(name):return json.loads((HERE/name).read_text(encoding='utf-8'))
def rgs(n,prefix=()):
    if not n:yield prefix;return
    for a in range(max(prefix,default=-1)+2):yield from rgs(n-1,prefix+(a,))
def induced(ds):
    vs=[0]
    for a in ds:vs.append(vs[-1]^(1<<a))
    return len(vs)==len(set(vs)) and all((vs[i]^vs[j]).bit_count()!=1 for i in range(len(vs)) for j in range(i+2,len(vs)))
def main():
    for n,path,count in [(7,'data/six/shapes.json',34),(8,'data/shapes.json',132)]:
        shapes=[list(s) for s in rgs(n) if induced(s)]
        assert shapes==read(path) and len(shapes)==count
        folder=HERE/Path(path).parent
        rows=[json.loads(p.read_text()) for p in sorted(folder.glob('window-*.json'))]
        assert len(rows)==count and all(r['status']=='UNSAT' for r in rows)
        assert [r['dirs'] for r in rows]==shapes
    log=(HERE/'logs/FamilyCoverage.log').read_text(encoding='utf-8')
    assert log.count('depends on axioms:')==3
    assert all(s not in log for s in ('sorryAx','Lean.ofReduceBool','error:'))
    up=read('data/upstream.json');p=HERE/'upstream/WindowAutomatonDefs.lean'
    assert hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()==up['sha256_lf']
    cuts=0;positive=[];unknown=[]
    for p in (HERE/'data').rglob('*.json'):
        r=json.loads(p.read_text())
        if not isinstance(r,dict) or 'status' not in r:continue
        for cc in r.get('cycle_cuts',[]):prior.check_cut(cc);cuts+=1
        if r.get('selected'):
            c=prior.census(r)
            assert all(c[k]==r['census'][k] for k in ['alpha','share','total_share','cycles'])
            positive.append(str(p.relative_to(HERE)))
        if r['status'] in ['UNKNOWN','TIME_LIMIT']:unknown.append(str(p.relative_to(HERE)))
    assert read('data/five-positive.json')['status']=='SAT'
    assert read('data/five-fixed-cp.json')['status']=='FEASIBLE'
    bank=read('data/bank-runs.json');assert bank['verified_snakes']==131 and bank['maximum_run_found']==2
    assert hashlib.sha256((ROOT/'work/bank9.json').read_bytes()).hexdigest()==bank['bank_sha256']
    result=dict(status='PASSED',solver_screen_exclusions={'seven_centres':132,'six_centres':34},lean_coverage_audits=3,
                cycle_cuts_checked=cuts,positive_records=positive,unknown_records=unknown,
                bank_maximum_run=2,scope='Experimental evidence only. Six-count-four universal exclusion remains a hypothesis; see proof-verification.json for four completed replays and the conditional universal bridges.')
    (HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
