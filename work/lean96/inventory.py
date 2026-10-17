"""Inventory Git evidence and propose a translation cover, without claiming proofs."""
from common import *
import subprocess
from build_regrowth_cnf import encode

def main():
    bank=read(ROOT/'work/bank9.json')
    assert len(bank)==131
    old=read(ROOT/'outputs/keep96/results.json')['entries']
    rows={};sets=[]
    for i in range(262):
        path=bank[i//2]['vertex_sequence'];path=path[::-1] if i%2 else path
        d=formula(i);fresh=encode(path,keep=96,total_vertices=193)
        assert d['clauses']==fresh['clauses'] and d['reasons']==fresh['reasons']
        assert d['prefix']==path[:96] and d['target']==98
        r=old[i];assert r['entry']==i
        cert=ROOT/r['certificate'] if r['certificate'] else None
        present=bool(cert and cert.exists())
        if present:assert sha(cert)==r['certificate_sha256']
        rows[str(i)]=dict(formula=f'outputs/keep96/formulas/entry{i:03d}.json.gz',
            formula_sha256=sha(ROOT/f'outputs/keep96/formulas/entry{i:03d}.json.gz'),
            cnf=f'outputs/keep96/formulas/entry{i:03d}.cnf.gz',
            cnf_sha256=sha(ROOT/f'outputs/keep96/formulas/entry{i:03d}.cnf.gz'),
            prior_solver_status=r['status'],certificate=r['certificate'] if present else None,
            certificate_sha256=r['certificate_sha256'] if present else None,
            certificate_present=present,certificate_bytes=r['certificate_bytes'],
            historical_result=r['result'])
        sets.append(frozenset(v^d['head'] for v in d['vertices']))
    unique=list(dict.fromkeys(sets));maximal=[s for s in unique if not any(s<t for t in unique)]
    def cost(i):return (not rows[str(i)]['certificate_present'],rows[str(i)]['certificate_bytes'],i)
    reps=[min([i for i,s in enumerate(sets) if s==t],key=cost) for t in maximal]
    reps.sort(key=cost)
    mapping={}
    for i,s in enumerate(sets):
        rep=i if i in reps else min([r for r in reps if s<=sets[r]],key=cost)
        mapping[str(i)]=dict(representative=rep,translation=formula(i)['head']^formula(rep)['head'])
    save(OUT/'survey.json',dict(entries=rows,scope='Historical solver results only; missing certificates require bounded regeneration.'))
    save(OUT/'cover.json',dict(representatives=reps,entries=mapping,status='PROPOSED_NOT_CERTIFIED'))
    save(OUT/'inventory.json',dict(time=now(),baseline=subprocess.check_output(['git','rev-parse','origin/research/dfs-lean-completion'],text=True).strip(),
        entries=262,available_certificates=sum(r['certificate_present'] for r in rows.values()),
        missing_certificates=[int(i) for i,r in rows.items() if not r['certificate_present']],
        unknown_entries=[int(i) for i,r in rows.items() if r['prior_solver_status']=='UNKNOWN'],
        representatives=len(reps),first_representative=reps[0],
        geometric_obligations='97-edge suffix, 98 distinct vertices, 49 of each parity; exact input clauses; every translated inclusion and bank-prefix identity checked in Lean.',
        reported_300second_followup='Not found in remote evidence; not counted.'))
    print(json.dumps(read(OUT/'inventory.json'),indent=2))

if __name__=='__main__':main()
