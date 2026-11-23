"""Compile integer star/face option tables from previously published price records."""
from pathlib import Path
from collections import defaultdict
from itertools import combinations
import functools
import json
BASE=Path(__file__).resolve().parent
ROOT=BASE.parent
def geometry(path):
    assert len(set(path))==len(path)
    assert all(((a^b).bit_count()==1)==(i+1==j) for i,a in enumerate(path) for j,b in enumerate(path) if j>i)

def factors(c):
    p=[0]
    for ch in c['word']:p.append(p[-1]^1<<int(ch))
    geometry(p)
    inside=set(p[1:-1]);ends={p[0],p[-1]}
    pool=((set(range(512))-inside)-{v^1<<a for v in inside for a in range(9)})|ends
    scale=c['scale'];maj=c['majority'];fees=c['fees'];axes=c['axes'];price={tuple(t[:3]):t[3] for t in c['weights']}
    sign=lambda v:1-2*(v.bit_count()%2)
    base=len(inside)*scale+2*fees[maj]+(1-2*maj-sum(map(sign,inside)))*fees[2]
    groups=[];compatible={}
    for v in sorted(pool):
        neighbors=[v^1<<i for i in range(9) if v^1<<i in pool]
        scope=[v]+neighbors;opts=[]
        for k in range(1<<len(neighbors)):
            sig=sum(v^n for i,n in enumerate(neighbors) if k>>i&1)
            if v not in ends:opts.append((2*k,0))
            degree=sig.bit_count()+(v in ends)
            if degree not in (1,2):continue
            val=scale-sign(v)*fees[2]-(fees[v.bit_count()%2] if degree==1 else 0)
            val+=sum(price.get((m,v,sig&m),0) for m in axes)
            opts.append((2*k+1,val))
            for m in axes:compatible.setdefault((v,m),set()).add(sig&m)
        groups.append((scope,opts))
    for m in axes:
        cells=defaultdict(list)
        for v in sorted(pool):cells[v&~m].append(v)
        for cell in cells.values():
            pos={v:i for i,v in enumerate(cell)}
            neighbors=[[u for u in cell if (u^v).bit_count()==1] for v in cell]
            adjacency=[sum(1<<pos[u] for u in ns) for ns in neighbors]
            must=sum(1<<pos[v] for v in ends if v in pos);opts=[]
            for k in range(1<<len(cell)):
                if k&must!=must:continue
                todo=k;value=0
                while todo:
                    bit=todo&-todo;todo-=bit;i=bit.bit_length()-1;v=cell[i]
                    sig=sum(v^u for u in neighbors[i] if k>>pos[u]&1)
                    if sig not in compatible.get((v,m),()):break
                    value-=price.get((m,v,sig),0)
                else:
                    left=k
                    while left:
                        stack=left&-left;deg=vertices=0
                        while stack:
                            bit=stack&-stack;stack-=bit;i=bit.bit_length()-1;left-=bit
                            ns=adjacency[i]&k;deg+=ns.bit_count();vertices+=1
                            stack|=ns&left
                        if deg!=2*(vertices-1):break
                    else:opts.append((k,value))
            groups.append((cell,opts))
    assert base+sum(max(v for k,v in opts) for _,opts in groups)==c['bound_scaled']
    return base,inside,ends,pool,groups

def save(tag,c):
    (BASE/(tag+'.json')).write_text(json.dumps(c,separators=(',',':')))
    base,inside,ends,pool,groups=factors(c)
    with (BASE/(tag+'.tables')).open('w') as f:
        print(base,c['scale'],c['bound_scaled'],len(groups),len(pool),len(inside),c['majority'],file=f)
        print(*sorted(pool),file=f);print(*sorted(inside),file=f)
        for cell,opts in groups:
            print(len(cell),len(opts),*cell,file=f)
            for k,s in sorted(opts,key=lambda z:-z[1]):print(k,s,file=f)
    return len(pool),len(groups),sum(len(o) for s,o in groups)

if __name__=='__main__':
    certificates={}
    for f in ['q9_facet_bank_all8.jsonl','q9_facet_bank_pilot.jsonl','q9_facet_bank_four.jsonl','q9_facet_191_donors_four.jsonl','q9_facet_bank_primal.jsonl']:
        for line in (ROOT/f).read_text().splitlines():
            if not line.endswith('}'):continue
            c=json.loads(line)
            if c['index'] not in (0,15,606) or 'bound_scaled' not in c:continue
            key=(c['index'],c['majority'])
            if key not in certificates or c['bound_scaled']<certificates[key][1]['bound_scaled']:certificates[key]=(f,c)
    for (i,m),(f,c) in sorted(certificates.items()):
        tag=f'i{i}m{m}';print(tag,f,c['bound_scaled'],*save(tag,c),flush=True)
    c=json.loads((ROOT/'q9_facet_bank_replay_positive.jsonl').read_text());print('control',*save('control',c),flush=True)
