"""Bounded, resumable experiments for two saturated empty Q9 faces. No trusted proofs."""
import argparse
import collections
import datetime as dt
import hashlib
import itertools as it
import json
import math
import os
from pathlib import Path
import platform
import subprocess
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
BASE = '53a47850c564fced0fd7e528636521ba859e1120'
N = 9

def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def write(p, obj):
    p = Path(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(p.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    tmp.replace(p)

def vertices(f):
    a,b,q = f
    assert a<b and q & ((1<<a)|(1<<b)) == 0
    return {q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}

def all_faces():
    for a,b in it.combinations(range(N),2):
        for q in range(1<<N):
            if q & ((1<<a)|(1<<b)) == 0:
                yield (a,b,q)

def layers(f):
    return [(k,{x^(1<<k) for x in vertices(f)}) for k in range(N) if k not in f[:2]]

def shell(f):
    return set().union(*(s for _,s in layers(f)))

def cls(q,r):
    overlap = len(set(q[:2]) & set(r[:2]))
    dist = min((x^y).bit_count() for x in vertices(q) for y in vertices(r))
    return f'P{overlap}D{dist}'

def classify():
    q=(0,1,0)
    counts=collections.Counter(cls(q,r) for r in all_faces() if r!=q)
    rows=[]
    for r in range(3):
        b=(2,3) if r==0 else (0,2) if r==1 else (0,1)
        fixed=[k for k in range(N) if k not in {0,1,*b}]
        for d in range(0 if r<2 else 1, len(fixed)+1):
            other=(*b,sum(1<<k for k in fixed[:d]))
            Q,R=vertices(q),vertices(other)
            B,C=shell(q),shell(other)
            key=cls(q,other)
            count=math.comb(2,r)*math.comb(7,2-r)*2**(2-r)*math.comb(5+r,d)
            assert count==counts[key]
            capq=sum(min(3,4-len(s&R)) for _,s in layers(q))
            capr=sum(min(3,4-len(s&Q)) for _,s in layers(other))
            rows.append(dict(id=key,r=r,d=d,Q=q,R=other,count_with_fixed_Q=count,
                face_intersection=sorted(Q&R),shell_intersection=sorted(B&C),
                R_in_Q_shell=sorted(R&B),Q_in_R_shell=sorted(Q&C),
                Q_cap_from_R_empty=capq,R_cap_from_Q_empty=capr))
    assert len(rows)==20 and sum(x['count_with_fixed_Q'] for x in rows)==4607
    return rows

def face_info(f,S):
    F=vertices(f)
    misses=[]
    for k,L in layers(f):
        absent=sorted(L-S)
        if len(absent)==1:
            a,b,q=f
            c=absent[0]^(1<<k)^q
            misses.append(dict(normal=k,corner=c,local_parity=c.bit_count()%2))
    return dict(face=f,empty=not bool(F&S),b=len(shell(f)&S),misses=misses,
                mixed=len({m['local_parity'] for m in misses})==2)

def scan(path):
    S=set(path)
    sat=[]
    hist=collections.Counter()
    s0=T=H=0
    for f in all_faces():
        k=len(vertices(f)&S)
        T+=k==1
        if k==0:
            b=len(shell(f)&S)
            hist[b]+=1
            s0+=1
            H+=b
            if b==21:
                sat.append(face_info(f,S))
    return dict(vertices=len(path),edges=len(path)-1,s0=s0,E=4*s0,T=T,H=H,
        D=21*s0-H,saturated=sat,b_histogram=dict(sorted(hist.items())),
        pairs=[dict(Q=q['face'],R=r['face'],id=cls(q['face'],r['face'])) for q,r in it.combinations(sat,2)])

def archived_scan():
    rows=[]
    for p in sorted((ROOT/'milestones/22-empty-square-tradeoff/runs').rglob('*.json')):
        obj=json.loads(p.read_text(encoding='utf-8'))
        result=obj.get('result',{}) if isinstance(obj,dict) else {}
        witness=result.get('witness',{})
        if isinstance(witness,dict) and 'path' in witness:
            path=witness['path']
            rows.append(dict(source=str(p.relative_to(ROOT)),source_sha256=sha(p),path=path,census=scan(path)))
    return rows

def solve(spec, logpath, modelpath):
    from ortools.sat.python import cp_model
    import ortools
    model=cp_model.CpModel()
    Q,R=tuple(spec['Q']),tuple(spec['R'])
    core=vertices(Q)|vertices(R)|shell(Q)|shell(R)
    U=set(range(512)) if spec['mode']=='global' else core|{v^(1<<k) for v in core for k in range(N)}
    x={v:model.new_bool_var(f'x{v}') for v in sorted(U)}
    end={}
    for v in sorted(U):
        neighbors=[v^(1<<k) for k in range(N)]
        visible=[x[w] for w in neighbors if w in U]
        if all(w in U for w in neighbors):
            e=model.new_bool_var(f'end{v}')
            end[v]=e
            model.add(e<=x[v])
            model.add(sum(visible)==2-e).only_enforce_if(x[v])
        else:
            model.add(sum(visible)<=2).only_enforce_if(x[v])
    model.add(sum(end.values()) == 2 if spec['mode']=='global' else sum(end.values())<=2)
    for f in (Q,R):
        for v in vertices(f):
            model.add(x[v]==0)
        for _,L in layers(f):
            model.add(sum(x[v] for v in L)==3)
        if spec.get('mixed',False):
            # Under saturation each layer has one missing corner. Both local parities occur.
            odd_missing=sum(1-x[v] for k,L in layers(f) for v in L
                            if ((v^(1<<k)^f[2]).bit_count()%2)==1)
            model.add(odd_missing>=1)
            model.add(odd_missing<=6)
    for f in all_faces():
        F=vertices(f)
        if F<=U:
            model.add(sum(x[v] for v in F)<=3)
    if spec['mode']=='global':
        model.add(sum(x.values())>=spec['min_vertices'])
        if 'max_vertices' in spec:
            model.add(sum(x.values())<=spec['max_vertices'])
        arcs=[]
        for v in range(512):
            arcs.append((v+1,v+1,x[v].Not()))
            a,b=model.new_bool_var(f'start{v}'),model.new_bool_var(f'finish{v}')
            model.add(a+b==end[v])
            arcs.extend([(0,v+1,a),(v+1,0,b)])
            for k in range(N):
                w=v^(1<<k)
                arc=model.new_bool_var(f'arc{v}_{w}')
                model.add(arc<=x[v]); model.add(arc<=x[w])
                arcs.append((v+1,w+1,arc))
        model.add_circuit(arcs)
    if spec.get('hint'):
        H=set(spec['hint'])
        for v in x:
            model.add_hint(x[v],int(v in H))
    modelpath.write_text(str(model.proto),encoding='utf-8')
    solver=cp_model.CpSolver()
    solver.parameters.num_search_workers=1
    solver.parameters.random_seed=spec['seed']
    solver.parameters.max_time_in_seconds=spec['seconds']
    solver.parameters.max_memory_in_mb=512
    solver.parameters.log_search_progress=True
    solver.parameters.log_to_stdout=False
    with logpath.open('w',encoding='utf-8') as log:
        solver.log_callback=lambda s:(log.write(s+'\n'),log.flush())
        status=solver.solve(model)
        log.write(solver.response_stats()+'\n')
    out=dict(status=solver.status_name(status),solver='OR-Tools CP-SAT',version=ortools.__version__,
        seed=spec['seed'],threads=1,time_limit_seconds=spec['seconds'],memory_soft_limit_mb=512,
        model_sha256=sha(modelpath),model_file=modelpath.name,log_sha256=sha(logpath),
        wall_seconds=solver.wall_time,response=solver.response_stats(),visible_vertices=len(U))
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        S={v for v in x if solver.value(x[v])}
        out['selected']=sorted(S)
        out['faces']=[face_info(f,S) for f in (Q,R)]
        if spec['mode']=='global':
            adj={v:[v^(1<<k) for k in range(N) if v^(1<<k) in S] for v in S}
            eps=[v for v in S if len(adj[v])==1]
            assert len(eps)==2
            path=[min(eps)]
            while len(path)<len(S):
                nxt=[w for w in adj[path[-1]] if len(path)==1 or w!=path[-2]]
                assert len(nxt)==1 and nxt[0] not in path
                path.append(nxt[0])
            out['path']=path
            out['census']=scan(path)
    return out

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--run',required=True)
    ap.add_argument('--mode',choices=['inventory','local','global'],required=True)
    ap.add_argument('--classes',nargs='*')
    ap.add_argument('--seconds',type=float,default=10)
    ap.add_argument('--min-vertices',type=int,default=28)
    ap.add_argument('--max-vertices',type=int)
    ap.add_argument('--mixed',action='store_true')
    args=ap.parse_args()
    run=HERE/'runs'/args.run
    run.mkdir(parents=True,exist_ok=True)
    lock=run/'RUNNING.lock'
    fd=os.open(lock,os.O_CREAT|os.O_EXCL|os.O_WRONLY)
    os.write(fd,json.dumps(dict(pid=os.getpid(),start=now())).encode()); os.close(fd)
    git=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    def case(name,spec,fn):
        p=run/(name+'.json')
        if p.exists():
            old=json.loads(p.read_text(encoding='utf-8'))
            assert old['code_sha256']==sha(__file__), 'Code changed: choose a new run id.'
            assert old['input_sha256']==hashlib.sha256((json.dumps(spec,ensure_ascii=False,indent=2)+'\n').encode()).hexdigest()
            print('SAVED',name,flush=True)
            return
        write(run/(name+'.input.json'),spec)
        write(run/'status.json',dict(pid=os.getpid(),case=name,updated=now(),running=True))
        start=time.monotonic()
        try:
            out=fn()
        except BaseException as e:
            write(run/(name+'.failure.json'),dict(error=repr(e),time=now(),code_sha256=sha(__file__)))
            raise
        write(p,dict(base_git=BASE,run_git=git,code_sha256=sha(__file__),
            input_sha256=sha(run/(name+'.input.json')),python=platform.python_version(),
            started_by_pid=os.getpid(),finished=now(),elapsed_seconds=time.monotonic()-start,result=out))
        print(name, out.get('status','COMPLETE') if isinstance(out,dict) else 'COMPLETE',flush=True)
    try:
        rows=classify()
        if args.mode=='inventory':
            case('classes',dict(n=N,definition='P=r free-coordinate intersection; D=minimum distance'),lambda:rows)
            case('archived',dict(source='milestone22 saved path witnesses; new pair census only'),archived_scan)
        else:
            for row in rows:
                key=row['id']
                if args.classes and key not in args.classes: continue
                spec=dict(mode=args.mode,Q=row['Q'],R=row['R'],id=key,seconds=args.seconds,
                    seed=20261020,min_vertices=args.min_vertices,mixed=args.mixed)
                if args.max_vertices is not None: spec['max_vertices']=args.max_vertices
                case(key,spec,lambda s=spec,k=key:solve(s,run/(k+'.log'),run/(k+'.model.txt')))
    finally:
        write(run/'status.json',dict(pid=os.getpid(),updated=now(),running=False))
        lock.unlink()

if __name__=='__main__': main()
