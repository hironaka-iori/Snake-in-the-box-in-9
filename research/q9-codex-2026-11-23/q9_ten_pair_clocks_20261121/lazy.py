"""Incremental geometric cuts over per-step physical axis choices."""
import sys,json
from pathlib import Path
from pysat.solvers import Cadical195
D=Path(__file__).resolve().parent
def solve(w,budget):
    # event anchors, state bits and global parity determine all nine coordinates.
    frames=[];kclock=[1,2,3,4];n=4;clauses=[[-x] for x in kclock];ph=[-x for x in kclock];active=set();parity=0;warm=0
    frames.append((parity,tuple(kclock)))
    for val in w:
        a=int(val);g=a//2;warm^=1<<a;parity^=1<<g
        if g<4:
            n+=1;kclock[g]=n;lit=(n if warm>>2*g&1 else -n);ph.append(lit)
            if g not in active:clauses.append([lit]);active.add(g)
        frames.append((parity,tuple(kclock)))
    def physical(frame,model):
        parity,clock=frame;x=(parity>>4)<<8
        for g,var in enumerate(clock):
            bit=int(var in model);x|=bit<<(2*g);x|=((parity>>g&1)^bit)<<(2*g+1)
        return x
    xors={};rows=set();iterations=0
    with Cadical195(bootstrap_with=clauses) as s:
        s.set_phases(ph)
        while True:
            cap=budget-s.accum_stats()['conflicts']
            if cap<=0:return 'LIMIT',None,len(rows),iterations
            s.conf_budget(cap);z=s.solve_limited();iterations+=1
            if z!=True:return ('UNSAT' if z is False else 'LIMIT'),None,len(rows),iterations
            model={v for v in s.get_model() if v>0};p=[physical(c,model) for c in frames];bad=[];occupied={}
            for j,v in enumerate(p):
                for u in (v,*(v^1<<k for k in range(9))):
                    for i in occupied.get(u,[]):
                        if j-i>1:bad.append((i,j))
                occupied.setdefault(v,[]).append(j)
            if not bad:return 'FOUND',p,len(rows),iterations
            had=0
            for i,j in bad:
                fi,vi=frames[i];fj,vj=frames[j];gap=fi^fj
                assert gap.bit_count()<=1
                refs=[]
                for g,(u,v) in enumerate(zip(vi,vj)):
                    if u==v or gap>>g&1:continue
                    key=(u,v)
                    if key not in xors:
                        n+=1;k=n;xors[key]=k
                        for q in ([-u,-v,-k],[u,v,-k],[-u,v,k],[u,-v,k]):s.add_clause(q)
                    refs.append(xors[key])
                key=tuple(refs)
                if key not in rows:rows.add(key);s.add_clause(refs);had+=1
            assert had
def main():
    src,mode,budget=sys.argv[1:];budget=int(budget);z=(D/(src+'.tsv')).read_text().splitlines()
    if mode=='all':ids=range(len(z))
    else:ids=[q['j'] for q in map(json.loads,(D/mode).read_text().splitlines()) if q['status'] in ('UNKNOWN','LIMIT')]
    for i in ids:
        s,p,c,it=solve(z[i].split()[-1],budget);print(json.dumps(dict(j=i,status=s,path=p,cuts=c,iterations=it),separators=(',',':')),flush=True)
        if p and len(p)>=193:break
if __name__=='__main__':main()
