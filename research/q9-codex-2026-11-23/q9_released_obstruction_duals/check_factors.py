"""Stdlib-only semantic verification of archived integer tables, followed by exact solver replay."""
from audit import *
import gzip,subprocess
from itertools import combinations
from collections import Counter

def check_tables(blob,c,fixed,D,h,goal):
    lines=iter(blob.decode().splitlines());hdr=list(map(int,next(lines).split()));i,t,e,scale,const,total,dsize,*tail=hdr;vertices=tail[:dsize];ng=tail[dsize]
    assert len(tail)==dsize+1 and set(vertices)==D and t==goal+1 and e==(h if h!=2 else 0)
    assert (i,scale,total)==(c['row'],c['scale'],c['numerator'])
    masks=[sum(1<<q for q in axis) for axis in c['axes']];w={(m,v,z):y for m,v,z,y in c['weights']};alpha,beta=c['end'],c['balance']
    assert const==2*alpha+((1-2*h)*beta if h!=2 else 0)
    vals={};headsum=const;nparsed=0
    def accept(scope,expected):
        nonlocal nparsed,headsum
        k,*s,kopts=map(int,next(lines).split());assert len(s)==k and s==scope and len(expected)==kopts
        actual=[tuple(map(int,next(lines).split())) for _ in range(kopts)]
        assert Counter(expected)==Counter(actual) and all(a[2]>=b[2] for a,b in zip(actual,actual[1:]))
        nparsed+=1;headsum+=actual[0][2]
    for v in sorted(D):
        ds=[1<<k for k in range(9) if v^(1<<k) in D];scope=[v]+[v^d for d in ds];full=(1<<len(scope))-1
        zs=[a+b for a,b in combinations(ds,2)]
        if h==2 or v.bit_count()%2==h:zs+=ds
        required=sum(d for d in ds if v^d in fixed)
        zs=[z for z in zs if (z&required)==required]
        vals[v]={m:{z&m for z in zs} for m in masks}
        opts=[] if v in fixed else [(0,1,0)]
        for z in zs:
            chosen=1+sum(1<<q for q,d in enumerate(ds,1) if z&d)
            price=scale-(1-2*(v.bit_count()%2))*beta-(alpha if z.bit_count()==1 else 0)+sum(w.get((m,v,z&m),0) for m in masks)
            opts.append((chosen,full^chosen,price))
        accept(scope,opts)
    for mask in masks:
        cells=defaultdict(list)
        for v in sorted(D):cells[v&~mask].append(v)
        for base,scope in sorted(cells.items()):
            opts=[];full=(1<<len(scope))-1
            for pattern in range(1<<len(scope)):
                T={v for j,v in enumerate(scope) if pattern>>j&1}
                if not (fixed&set(scope))<=T:continue
                ds={v:sum(v^u for u in T if (v^u).bit_count()==1) for v in T}
                if any(z not in vals[v][mask] for v,z in ds.items()):continue
                # Maximum degree is already at most two; a cycle is a connected component with no tip.
                seen=set()
                for s in T:
                    if s in seen:continue
                    q=[s];seen.add(s);deg_sum=0
                    for v in q:
                        deg_sum+=ds[v].bit_count()
                        for u in T-seen:
                            if (v^u).bit_count()==1:q.append(u);seen.add(u)
                    if deg_sum!=2*(len(q)-1):break
                else:
                    opts.append((pattern,full^pattern,-sum(w.get((mask,v,z),0) for v,z in ds.items())))
            accept(scope,opts)
    assert nparsed==ng and headsum==total and next(lines,None) is None

def main():
    import argparse
    a=argparse.ArgumentParser();a.add_argument('--radius',type=int,default=12);o=a.parse_args();r=o.radius
    sources=[f'branch{r}.jsonl',f'retry{r}a.jsonl',f'branch{r}p16.jsonl',f'branch{r}p24.jsonl']
    cases={i:f for _,i,f in fixed_cases(r)}
    verified=defaultdict(dict);count=0;replays=0
    for source in sources:
        path=HERE/source
        if not path.exists():continue
        for result in rows(path):
            h=result['signature'];n=result['row'];st=result['status']
            if st not in ('DUAL','EXHAUSTED'):continue
            f=cases[n];assert all(cases[j]==f for j in result['equivalent_rows'])
            g=193 if h==2 else 192;assert result['goal']==g
            if all(h in verified[j] for j in result['equivalent_rows']):continue
            parts=result.get('parts',8);cp=HERE/'certs'/f'r{r}_row{n}_h{h}_p{parts}.json'
            if not cp.exists():continue
            c=json.loads(cp.read_text());assert set(c['fixed'])==f and c['signature']==h and c['radius']==r
            P,D=close(f,set(),None,h);upper=value(c,P,D,g,h%2);assert upper==c['numerator']==result['numerator']
            if st=='DUAL':assert upper < (g+1)*c['scale']
            else:
                b=gzip.open(HERE/result['input'],'rb').read()
                check_tables(b,c,P,D,h,g)
                env={**os.environ,'Q9_PATH_MINIMUM':'1'};env.pop('Q9_AVOID_SHAPES',None)
                out=subprocess.run([str(HERE/'factor'),str(result['nodes']+1)],input=b,stdout=subprocess.PIPE,env=env,check=True).stdout.decode().split()
                assert list(out)==[str(n),'EXHAUSTED',str(result['nodes'])];replays+=1
            count+=1
            for j in result['equivalent_rows']:verified[j][h]=[st,n,result['nodes']]
    ws=[x['witness'] for file in ['q9_full_obstruction_191.jsonl','q9_break_matched_191.jsonl'] for x in rows(file) if x['status']=='FOUND']
    assert all(valid(p) and len(p)==192 for p in ws)
    wins={};excluded=[];exact=[];unknown=[]
    for j,f in cases.items():
        p=next((p for p in ws if f<=set(p)),None)
        if p:wins[j]=p
        if len(verified[j])==3:
            excluded.append(j)
            if p:exact.append(j)
        else:unknown.append(j)
    print(json.dumps(dict(radius=r,excluded=excluded,conditional_191_exact=exact,pending=unknown,replayed_complete_searches=replays,independently_checked_cases=count,verified_branches=verified,witnesses=wins),separators=(',',':')))
if __name__=='__main__':main()
