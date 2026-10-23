"""Check proof provenance, final axiom audits and positive local configurations."""
import gzip,hashlib,json
from pathlib import Path
from certify import HERE,ROOT,BOUNDS,TaggedEncoding,window,candidates,joint_literals,prior

def read(name):return json.loads((HERE/name).read_text(encoding='utf-8'))
def raw(name):
    p=HERE/'certificates'/name
    return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def clauses(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l.strip() and not l.startswith(('p','c'))]
def main():
    stats=[];audits=0
    for i,cap in [(3,27),(2,28)]:
        enc=TaggedEncoding(window(candidates()[i]['dirs']),BOUNDS,radius=4)
        enc.atmost(joint_literals(enc,enc.window),cap,('ends',))
        full=clauses(f'sum{i}.full.cnf');assert full[:len(enc.clauses)]==enc.clauses
        inv={v:k for k,v in enc.var.items()};cuts=[]
        for cl in full[len(enc.clauses):]:
            assert all(v<0 and -v in inv for v in cl)
            cc=[inv[-v] for v in cl];prior.check_cut(cc);cuts.append(sorted(cc))
        meta=read(f'data/sum{i}.json');assert sorted(cuts)==meta['cycle_cuts']
        rename={int(k):v for k,v in meta['original_to_new'].items()}
        expected=[[(-1 if v<0 else 1)*rename[abs(v)] for v in full[j-1]] for j in meta['source_original_clause_ids']]
        core=clauses(f'sum{i}.cnf');assert core==expected
        assert max(abs(v) for cl in core for v in cl)==meta['active_variables']
        assert 's VERIFIED' in (HERE/f'logs/sum{i}-drat-check.txt').read_text()
        proof=read(f'logs/sum{i}-export.txt');assert proof['simulated']
        stats.append(dict(case=i,cap=cap,clauses=len(core),variables=meta['active_variables'],cycle_cuts=len(cuts),hints=proof['hints']))
    for name,n in [('JointCountTags',10),('JointCountBridge',1),('WeightedExcess',3),
                   ('LocalWindowSat-JointSum3',1),('LocalWindowSat-JointSum2',1),('SumWindow3',2),('SumWindow2',2)]:
        log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
        assert log.count('depends on axioms:')==n,(name,log)
        assert all(bad not in log for bad in ('sorryAx','Lean.ofReduceBool','error:'))
        for line in log.splitlines():
            if 'depends on axioms:' in line:
                names=set(line.split('depends on axioms:',1)[1].strip().strip('[]').split(', '))
                assert names<={'propext','Classical.choice','Quot.sound'}
        audits+=n
    for r in read('data/archives.json'):
        assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
        assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
    positive=read('data/positive-2-30.json');p=prior.census(positive)
    assert p==positive['census'] and sum(p['alpha'][j] for j in [0,3,6])==30
    controls=[]
    for path in (HERE/'data').glob('positive-*.json'):
        row=json.loads(path.read_text())
        for cc in row['cycle_cuts']:prior.check_cut(cc)
        controls.append(dict(file=path.name,status=row['status'],cap=row['cap']))
    out=dict(status='PASSED',audited_theorems=audits,proofs=stats,total_lrat_hints=sum(r['hints'] for r in stats),
             proved_high_count_lower_bounds={'case2':29,'case3':28},case2_positive_counts=p['alpha'],
             further_tests=controls,scope='No new global upper bound. Case-2 cap-29 exclusion remains solver-only.')
    (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
