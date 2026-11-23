import json,hashlib
from pathlib import Path
from certify import cnf
from pysat.solvers import Solver
B=Path(__file__).resolve().parent;R=B.parent
def rows(p):return [json.loads(l) for l in p.read_text().splitlines()]
source=rows(R/'q9_uncovered_endpoint_relocation.jsonl')
orig=[(r,b['majority']) for r in source for b in r['branches'] if b['status']=='UNKNOWN']
ranks=json.loads((B/'rank.json').read_text());checked={r['rank']:r for r in rows(B/'proofs_checked.jsonl')}
assert len(orig)==len(checked)==len(ranks)==119 and set(checked)==set(range(119))
bank=(R/'q9_far189_spring_20261121/comparison191.words').read_text().split()
def geometry(p):
    assert len(set(p))==len(p) and all(0<=v<512 for v in p)
    assert all(((v^u).bit_count()==1)==(j-i==1) for i,v in enumerate(p) for j,u in enumerate(p) if i<j)
def key(r):return (r['archive'],r['side'],r['new_vertex'],r['radius'],r['majority'])
out=[]
for rank,(width,free,i) in enumerate(ranks):
    source_row,colour=orig[i];r=source_row|dict(majority=colour)
    tag='rank'+str(rank);a=checked[rank];actual=(B/(tag+'.cnf')).read_bytes()
    F=cnf(r);canonical=(F.to_dimacs()+'\n').encode()
    assert actual==canonical and hashlib.sha256(actual).hexdigest()==a['cnf_sha256']
    assert hashlib.sha256((B/(tag+'.drat')).read_bytes()).hexdigest()==a['proof_sha256']
    out.append(dict(rank=rank,archive=r['archive'],side=r['side'],new_vertex=r['new_vertex'],radius=r['radius'],majority=colour,
                    cnf_sha256=a['cnf_sha256'],drat_sha256=a['proof_sha256'],result=a['result']))
assert len({key(r) for r in out})==119
(B/'branch_manifest.jsonl').write_text(''.join(json.dumps(q)+'\n' for q in out))
control_results=[]
for file in ['control.jsonl','exactpins184.jsonl']:
    for r in rows(B/file):
        if r['status']!='FOUND':continue
        rank=r['rank'];src,_=orig[ranks[rank][2]];p=r['path'];geometry(p)
        assert all(r[k]==src[k] for k in ('archive','side','new_vertex','radius'))
        parent=[0]
        for d in bank[src['archive']]:parent.append(parent[-1]^(1<<int(d)))
        y=src['new_vertex'];ep=parent[-1] if src['side'] else parent[0]
        forbidden={u for u in parent if (u^y).bit_count()==1 and u!=ep}
        mandatory={u for u in parent if all((u^b).bit_count()>src['radius'] for b in forbidden)}|{ep}
        assert mandatory<=set(p)
        if not r['control']:
            assert y in p and not set(p)&forbidden and len(p)==185
            for n in [185,193]:
                F,x,t=cnf(r,n,True);ass=[v if q in p else -v for q,v in x.items()]
                with Solver(name='cadical195',bootstrap_with=F) as s:assert s.solve(assumptions=ass)==(n==185)
        else:assert len(p)==192
        control_results.append(dict(rank=rank,archive=r['archive'],edges=len(p)-1,new_pin_and_blockers_held=not r['control']))
print(json.dumps(dict(original_branches=sum(len(r['branches']) for r in source),previous_unknown=len(orig),regenerated_cnf_and_verified_drat=len(out),controls=control_results),indent=2))
