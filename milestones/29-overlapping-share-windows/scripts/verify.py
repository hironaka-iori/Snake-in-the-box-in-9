"""Check certificate provenance, exact join enumeration, archives and Lean audits."""
import gzip,hashlib,importlib.util,json,sys
from fractions import Fraction
from pathlib import Path
from joint import HERE,ROOT,candidates,TaggedEncoding,window,canonical,dkey

def read(name):return json.loads((HERE/name).read_text(encoding='utf-8'))
def raw(name):
    p=HERE/'certificates'/name
    return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def clauses(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l.strip() and not l.startswith(('p','c'))]
def main():
    cases=candidates();assert cases==read('data/candidates.json')
    proofstats=[]
    for i,case in enumerate(cases):
        enc=TaggedEncoding(window(case['dirs']),[(4,4)]*7,radius=4)
        plain=read(f'data/plain-{i}.json');assert plain['status']=='UNSAT' and plain['cycle_cuts']==[]
        assert clauses(f'joint{i}.full.cnf')==enc.clauses
        meta=read(f'data/joint{i}.json');rename={int(k):v for k,v in meta['original_to_new'].items()}
        ids=meta['source_original_clause_ids'];expected=[[(-1 if v<0 else 1)*rename[abs(v)] for v in enc.clauses[j-1]] for j in ids]
        actual=clauses(f'joint{i}.cnf');assert actual==expected
        assert max(abs(v) for c in actual for v in c)==meta['active_variables']
        assert 's VERIFIED' in (HERE/f'logs/joint{i}-drat-check.txt').read_text()
        audit=(HERE/f'logs/Window{i}.log').read_text(encoding='utf-8')
        assert audit.count('depends on axioms:')==2
        assert all(bad not in audit for bad in ('sorryAx','error:','Lean.ofReduceBool'))
        proofstats.append(json.loads((HERE/f'logs/joint{i}-export.txt').read_text()))
    for name,count in [('JoinClassification',2),('JointObstruction',1),('SelectiveMemory',4)]:
        audit=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
        assert audit.count('depends on axioms:')==count
        assert all(bad not in audit for bad in ('sorryAx','error:','Lean.ofReduceBool'))
    for r in read('data/archives.json'):
        p=HERE/'certificates'/r['file'];data=raw(r['file'])
        assert hashlib.sha256(data).hexdigest()==r['sha256']
        assert hashlib.sha256(p.with_name(p.name+'.gz').read_bytes()).hexdigest()==r['archive_sha256']
    graph=read('data/selective-graph.json')
    assert graph['states']==44132 and graph['added_states']==68 and graph['removed_edges']==4
    assert graph['script_sha256_lf']==hashlib.sha256((HERE/'scripts/selective_graph.py').read_bytes().replace(b'\r\n',b'\n')).hexdigest()
    special={dkey(c['dirs']) for c in cases}
    for run in graph['runs']:
        cyc=run['cycle']
        assert Fraction(sum(e['weight'] for e in cyc),120*len(cyc))==Fraction(run['mean'])
        for j,e in enumerate(cyc):
            assert e['next_state']==cyc[(j+1)%len(cyc)]['state']
            before=e['state'];after=e['next_state'];ds=e['directions'];a=e['alpha']
            assert tuple(before[0])==canonical(ds[:-1]) and tuple(after[0])==canonical(ds[1:])
            assert after[1]==before[1][1:]+[a]
            assert after[2]==(min(6,before[2]+1) if a==4 else 0)
            if run['stage']=='after':assert not(before[2]==6 and a==4 and dkey(ds) in special)
    spec=importlib.util.spec_from_file_location('prior_verify',ROOT/'milestones/28-direct-share-certificates/scripts/verify.py')
    prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
    frontier=[]
    for i in [2,3]:
        r=read(f'data/next-interval-{i}.json');c=prior.census(r)
        assert all(c[k]==r['census'][k] for k in ['alpha','share','total_share','cycles'])
        for cc in r['cycle_cuts']:prior.check_cut(cc)
        frontier.append(c['alpha'])
    result=dict(status='PASSED',geometric_exclusions=4,finite_classification_theorems=2,
                combined_theorems=1,selective_memory_theorems=4,audited_theorems=15,clauses=[len(clauses(f'joint{i}.cnf')) for i in range(4)],
                total_lrat_hints=sum(r['hints'] for r in proofstats),graph_cycle_means=[r['mean'] for r in graph['runs']],next_cycle_witness_counts=frontier,solver_only_six_centre_screen='Initial short runs UNKNOWN; two longer runs UNSAT without certificates.')
    (HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
