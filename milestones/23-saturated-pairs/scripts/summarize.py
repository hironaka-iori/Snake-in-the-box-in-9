"""Package new conclusions; retain all solver attempts, including superseded UNKNOWNs."""
import collections
import gzip
import hashlib
import itertools as it
import json
from pathlib import Path
import subprocess
import time
import pairs

HERE=pairs.HERE
ROOT=pairs.ROOT

def main():
    assert not (HERE/'analysis.json').exists(), 'Use a new evidence directory for a revised analysis.'
    started=time.monotonic()
    local={}
    attempts=[]
    witnesses={}
    checks={}
    for p in sorted((HERE/'checks').glob('independent-*.json')):
        for row in json.loads(p.read_text(encoding='utf-8'))['checks']:
            checks[str(Path(row['file']))]=row
    for folder in ('local-a','global-a','global-b','sharp-deficit-a'):
        for p in sorted((HERE/'runs'/folder).glob('P*.json')):
            if '.input.' in p.name or '.failure.' in p.name: continue
            obj=json.loads(p.read_text(encoding='utf-8'))
            spec=json.loads(p.with_name(p.stem+'.input.json').read_text(encoding='utf-8'))
            r=obj['result']; rel=str(p.relative_to(ROOT))
            attempts.append(dict(file=rel,id=p.stem,mode=spec['mode'],r_touch=spec.get('r_touch',21),
                status=r['status'],seconds=r['wall_seconds'],saved=obj['finished']))
            if folder=='local-a': local[p.stem]=r['status']
            if 'path' in r and spec.get('r_touch',21)==21:
                assert rel in checks and checks[rel]['status']=='PASS'
                witnesses[p.stem]=dict(file=rel,edges=len(r['path'])-1,path=r['path'],
                    faces=r['faces'],E=r['census']['E'],T=r['census']['T'])
    excluded={'P0D0':'forced eight-cycle','P1D0':'one layer loses two corners',
        'P1D1':'one layer loses two corners','P2D1':'one normal layer is empty',
        'P2D3':'C4 square C6 forest: pair capacity 39'}
    rows=[]
    for row in pairs.classify():
        key=row['id']
        rows.append(dict(**row,local_status=local[key],
            evidence='MATHEMATICAL_PROOF_NOT_LEAN' if key in excluded else 'INDEPENDENTLY_CHECKED_WITNESS_NOT_LEAN',
            reason=excluded.get(key),witness=witnesses.get(key)))
        assert key in excluded or key in witnesses
    # Check the new deficit and packing statements on every newly found true path.
    tests=[]
    for key,w in sorted(witnesses.items()):
        S=set(w['path']); empty={}
        for f in pairs.all_faces():
            if not (pairs.vertices(f)&S): empty[f]=len(pairs.shell(f)&S)
        sat=[f for f,b in empty.items() if b==21]
        assert all(not(pairs.vertices(f)&pairs.vertices(g)) for f,g in it.combinations(sat,2))
        v=len(S); M=len(sat); s0=len(empty); H=sum(empty.values()); D=21*s0-H
        assert 4*M<=512-v and 21*M<=7*v+2 and M<=73
        e3=0; maximum=0
        for f,b in empty.items():
            normals=[k for k in range(9) if k not in f[:2]]
            for triple in it.combinations(normals,3):
                g=(f[0],f[1],f[2]^sum(1<<k for k in triple))
                if g in empty and f<g:
                    e3+=1; maximum=max(maximum,b+empty[g]); assert b+empty[g]<=39
        assert 35*D>=3*e3 and D>=s0-M
        tests.append(dict(id=key,v=v,s0=s0,H=H,D=D,M=M,e3=e3,
                          maximum_parallel_distance3_pair_sum=maximum,status='PASS'))
    # An explicit extension of the already-saved m=238 count/direction relaxation.
    old=ROOT/'milestones/22-empty-square-tradeoff/runs/finite-obstruction.json'
    obstruction=json.loads(old.read_text(encoding='utf-8'))
    assert (obstruction['m'],obstruction['v'],obstruction['T'],obstruction['E'])==(238,239,835,28)
    labels=[(0,1,(1<<2)|(1<<k)) for k in range(3,9)]+[(0,1,(1<<3)|(1<<4))]
    assert len(set(labels))==7
    assert all(pairs.cls(f,g) not in excluded for f,g in it.combinations(labels,2))
    assert 28+2*835+70*239==18428 and 28+77*238<=18394
    gate=[]
    for m in (238,237,236):
        v=m+1; smax=(18394-77*m)//4
        mbound=min(v//3,(512-v)//4)
        gate.append(dict(m=m,v=v,s0_max_from_238_chain=smax,M_bound_without_s0=mbound,
            sufficient_E=4*(smax+1),needed_H_plus_D=21*smax+1,
            needed_H_if_all_faces_b_at_most_20=20*smax+1,
            packing_bound_active=False))
        assert smax<mbound
    pairs.write(HERE/'analysis.json',dict(code_sha256=pairs.sha(__file__),
        dependency_sha256=pairs.sha(pairs.__file__),run_git=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        created=pairs.now(),seconds=time.monotonic()-started,classes=rows,
        solver_attempts=attempts,attempt_counts=dict(collections.Counter(a['status'] for a in attempts)),
        independently_checked_witnesses=len(witnesses),lemma_tests=tests,value_gate=gate,
        abstract_obstruction=dict(source=str(old.relative_to(ROOT)),source_sha256=pairs.sha(old),
            m=238,v=239,E=28,T=835,empty_face_labels=labels,
            extension1=dict(b_each=20,M=0,H=140,D=7,e3=0,e00=0),
            extension2=dict(b_each=21,M=7,H=147,D=0,e3=0,e00=0),
            status='COUNT_AND_PAIR_RELAXATION_ONLY_NOT_A_REAL_SELECTED_SET'),
        new_global_bound=False,new_Lean_proof=False,
        unresolved=['Sharpness of 39: the b(Q)=21,b(R)=18 search was UNKNOWN',
                    'Independent H lower bound related to T,v',
                    'Forced lower bound on e3 or K3 for near-bound paths',
                    'Joint realization of many pairwise-compatible saturated faces']))
    print('classes',len(rows),'human exclusions',len(excluded),'checked witnesses',len(witnesses))
    print('attempts',dict(collections.Counter(a['status'] for a in attempts)))
    print('value gate',gate)

if __name__=='__main__': main()
