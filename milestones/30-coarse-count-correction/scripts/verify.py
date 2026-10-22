"""Certificate provenance, positive witnesses, cycle cuts and overlap diagnostics.

Lean audits are checked for standard axioms; this script does not replace Lean.
No solver-only infeasibility is promoted to a theorem by this verifier.
"""
import gzip, hashlib, importlib.util, itertools, json, sys
from fractions import Fraction
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,canonical
from correction_graph import advance,periodic,trailing

def read(name):return json.loads((HERE/name).read_text(encoding='utf-8'))
def digest(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def raw(name):
    p=HERE/'certificates'/name
    return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def clauses(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l.strip() and not l.startswith(('p','c'))]

def main():
    hints=0;clause_counts=[];audits=0
    cases=read('data/cases.json')
    for i,c in enumerate(cases):
        enc=TaggedEncoding(window(c['dirs']),c['bounds'],radius=4)
        assert clauses(f'coarse{i}.full.cnf')==enc.clauses
        meta=read(f'data/coarse{i}.json');rename={int(k):v for k,v in meta['original_to_new'].items()}
        expected=[[(-1 if v<0 else 1)*rename[abs(v)] for v in enc.clauses[j-1]] for j in meta['source_original_clause_ids']]
        actual=clauses(f'coarse{i}.cnf');assert actual==expected
        assert max(abs(v) for c in actual for v in c)==meta['active_variables']
        assert 's VERIFIED' in (HERE/f'logs/coarse{i}-drat-check.txt').read_text()
        stats=read(f'logs/coarse{i}-export.txt');assert stats['simulated'];hints+=stats['hints']
        clause_counts.append(len(actual))
    for name,n in [(f'Window{i}',2) for i in range(4)]+[('ExcessArithmetic',8),('ExcessGeometry',3)]:
        log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
        assert log.count('depends on axioms:')==n,(name,log)
        assert all(s not in log for s in ['error:','sorryAx','Lean.ofReduceBool'])
        for line in log.splitlines():
            if 'depends on axioms:' in line:
                names=line.split('depends on axioms:',1)[1].strip().strip('[]').split(', ')
                assert set(names)<={'propext','Classical.choice','Quot.sound'}
        audits+=n
    for r in read('data/archives.json'):
        assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
        assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
    spec=importlib.util.spec_from_file_location('prior',ROOT/'milestones/28-direct-share-certificates/scripts/verify.py')
    prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
    checked_cuts=0;witnesses=[];solver_only=[]
    for p in sorted((HERE/'data').glob('*.json')):
        if not p.name.startswith(('excess-','independent-')):continue
        r=json.loads(p.read_text())
        for cc in r['cycle_cuts']:prior.check_cut(cc);checked_cuts+=1
        if r.get('selected'):
            c=prior.census(r)
            for k,v in c.items():assert r['census'][k]==v,(p.name,k)
            assert sum(c['alpha'][j] for j in [0,3,6])<=r['cap']
            witnesses.append(dict(file=p.name,alpha=c['alpha']))
        solver_only.append(dict(file=p.name,status=r['status'],cap=r['cap']))
    controls=read('data/counter-controls.json');assert controls['status']=='PASSED' and len(controls['rows'])==4
    assert all(r['sat']==(r['cap']==r['exact']) for r in controls['rows'])
    graph=read('data/selective-graph.json');assert graph['script_sha256_lf']==digest(HERE/'scripts/correction_graph.py')
    assert graph['states']==44336 and graph['removed_edges']==2 and graph['corrected_edges']==2
    phase=[(3,3,6,3,3,6,3),(3,6,3,3,6,3,3),(6,3,3,6,3,3,6)]
    from packing import key
    ck=[key(c['dirs'],tuple((z,z) if z<6 else (6,21) for z in phase[min(i,2)])) for i,c in enumerate(cases)]
    for run in graph['runs']:
        cyc=run['cycle'];n=len(cyc)
        assert Fraction(sum(e['weight'] for e in cyc),360*n)==Fraction(run['mean'])
        for j,e in enumerate(cyc):
            before=e['state'];after=e['next_state'];ds=e['directions'];a=e['alpha']
            assert after==cyc[(j+1)%n]['state']
            assert tuple(before[0])==canonical(ds[:-1]) and tuple(after[0])==canonical(ds[1:])
            assert after[1]==before[1][1:]+[a]
            assert tuple(after[2:])==advance(tuple(before[1]),*before[2:],a)
            history=tuple(cyc[(j+t)%n]['alpha'] for t in range(-14,0))
            assert before[1]==list(history[-4:])
            assert before[2:]==[min(6,trailing(history)),min(6,periodic(history))]
            seven=(history+(a,))[-7:]
            k=key(ds,tuple((z,z) if z<6 else (6,21) for z in seven))
            if run['stage']=='after':assert k not in ck[:2]
            expected=120 if run['stage']=='after' and k in ck[2:] else 0
            assert e['excess_bonus']==expected and e['weight']==e['base_weight']+expected
    # Exhaust all 4^8 reduced-alphabet histories, then all six next symbols.
    # Other symbols have identical behavior because only 3,4,6 are distinguished.
    histories=0
    for h in itertools.product([1,3,4,6],repeat=8):
        for a in range(1,7):
            got=advance(h[-4:],min(6,trailing(h)),min(6,periodic(h)),a)
            assert got==(min(6,trailing(h+(a,))),min(6,periodic(h+(a,))))
            histories+=1
    out=dict(status='PASSED',audited_theorems=audits,geometric_exclusions=4,
             clauses=clause_counts,total_lrat_hints=hints,cycle_cuts_checked=checked_cuts,
             positive_witnesses=witnesses,counter_controls=4,history_transitions_checked=histories,
             exact_cycle_means=[r['mean'] for r in graph['runs']],solver_only=solver_only,
             scope='No new global upper bound. Strong sum-cap exclusions remain solver-only.')
    (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
