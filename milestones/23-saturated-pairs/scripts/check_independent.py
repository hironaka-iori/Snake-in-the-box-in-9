"""Independent checks: no import of the generator/model or its face routines."""
import argparse
from collections import Counter
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import platform
import subprocess
import time

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def bits(v): return tuple(int(c) for c in format(v,'09b')[::-1])

def distance(u,v): return sum(a!=b for a,b in zip(bits(u),bits(v)))

def corners(f):
    a,b,base=f
    out=[]
    for i,j in product((0,1),repeat=2):
        z=list(bits(base)); z[a]=i; z[b]=j
        out.append(sum(x*2**k for k,x in enumerate(z)))
    return out

def inspect_face(f,S):
    F=corners(f)
    B={v for v in range(512) if v not in F and any(distance(v,w)==1 for w in F)}
    missed=[]
    for k in range(9):
        if k not in f[:2]:
            missing=[w for w in F if (w^(2**k)) not in S]
            missed.append({'normal':k,'missing_corners':missing,
                           'local_parities':[(bits(w)[f[0]]+bits(w)[f[1]])%2 for w in missing]})
    return {'empty':not(S&set(F)),'b':len(S&B),'missed':missed}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--runs',nargs='+',required=True)
    ap.add_argument('--output',required=True); args=ap.parse_args()
    output=HERE/args.output
    assert not output.exists(), 'Preserve prior checks; choose a new output.'
    start=time.monotonic(); rows=[]
    for run in args.runs:
        for p in sorted((HERE/'runs'/run).glob('P*.json')):
            if '.input.' in p.name or '.failure.' in p.name: continue
            obj=json.loads(p.read_text(encoding='utf-8')); result=obj['result']
            if 'path' not in result: continue
            spec=json.loads(p.with_name(p.stem+'.input.json').read_text(encoding='utf-8'))
            path=result['path']; S=set(path)
            assert len(path)==len(S) and all(0<=v<512 for v in path)
            for i,j in combinations(range(len(path)),2):
                assert (distance(path[i],path[j])==1)==(j==i+1),(p,i,j)
            assert len(path)>=spec['min_vertices']
            if 'max_vertices' in spec: assert len(path)<=spec['max_vertices']
            faces=[inspect_face(spec[k],S) for k in ('Q','R')]
            assert all(f['empty'] for f in faces)
            assert faces[0]['b']==21 and faces[1]['b']==spec.get('r_touch',21)
            if len(path)>27:
                for f in faces:
                    if f['b']==21:
                        assert {m['local_parities'][0] for m in f['missed']}=={0,1}
            # Anchored census, divided by 4 (empty), singleton counted only at its selected corner.
            E=T=0
            for base in range(512):
                for a,b in combinations(range(9),2):
                    F={base,base^2**a,base^2**b,base^2**a^2**b}
                    E+=not bool(F&S)
                    T+=(base in S and len(F&S)==1)
            assert E+2*T+70*len(path)==18428
            assert E==result['census']['E'] and T==result['census']['T']
            rows.append(dict(file=str(p.relative_to(ROOT)),sha256=digest(p),status='PASS',
                             vertices=len(path),edges=len(path)-1,faces=faces,E=E,T=T))
            print(p.parent.name,p.stem,'PASS',len(path)-1,flush=True)
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(dict(evidence='Independent finite computation; not Lean',
        code_sha256=digest(Path(__file__)),git=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        python=platform.python_version(),seconds=time.monotonic()-start,checks=rows),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

if __name__=='__main__': main()
