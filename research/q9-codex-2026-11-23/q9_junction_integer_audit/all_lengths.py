"""Unconditional geometric propagation for each of the three endpoint signatures."""
import json
import os
from pathlib import Path
from verify import ROOT, HERE, N, COLOUR, V, value, rows

def unbounded(anchors, ep):
    fixed, avail = set(anchors), set(V)
    budget = [1,1] if ep==2 else [2*(ep==h) for h in (0,1)]
    while True:
        deg={v:len(avail&N[v]) for v in avail}
        reserved={v for v in fixed if deg[v]==1}
        spare=[budget[h]-len(reserved&COLOUR[h]) for h in (0,1)]
        assert min(spare)>=0
        sat={v for v in fixed if len(N[v]&fixed)==2}
        assert all(len(N[v]&fixed)<=2 for v in fixed)
        comp={}
        for start in fixed:
            if start in comp:continue
            todo=[(start,None)]
            while todo:
                v,p=todo.pop()
                assert v not in comp
                comp[v]=start
                todo.extend((n,v) for n in N[v]&fixed if n!=p)
        take,drop=set(),set()
        for v in avail:
            mindeg=1 if v in reserved or spare[v.bit_count()%2] else 2
            if v in fixed:
                assert deg[v]>=mindeg
                if deg[v]==mindeg:take|=N[v]&avail
            else:
                neighbours=N[v]&fixed
                if len(neighbours)>2 or neighbours&sat or len({comp[w] for w in neighbours})<len(neighbours) or deg[v]<mindeg:drop.add(v)
        assert not (take|fixed)&drop
        if take<=fixed and not drop:return fixed,avail
        fixed|=take;avail-=drop

def main():
    import sys
    from search_q9_shell_dual import build
    out=HERE/'unbounded_duals'
    out.mkdir(exist_ok=True)
    F=set(rows(ROOT/'q9_junction_first_omission.jsonl')[0]['fixed'])
    if len(sys.argv)>1:
        c=json.loads(Path(sys.argv[1]).read_text());F=set(c['fixed'])
    for h in (2,0,1):
        P,D=unbounded(F,h)
        # 'goal' chooses only bipartition signed sum and permitted endpoint colours in build/value.
        g, ep = (193,0) if h==2 else (192,h)
        for parts in (16,26,40,64,84):
            os.environ['Q9_SHELL_PARTS']=str(parts)
            r=build(sorted(F),0,ep,g,P,D)
            c=r[-1];a=value(c,P,D,g,ep)
            assert a==r[1]
            c.update(upper=a,fixed=sorted(F),signature=h,forced=len(P),allowed=len(D))
            name=f'all{len(F)}_{sum(F)}_h{h}_n{parts}.json'
            (out/name).write_text(json.dumps(c,separators=(',',':')))
            print(json.dumps({'certificate':name,'ep':h,'numerator':a,'scale':c['scale'],'forced':len(P),'domain':len(D)}),flush=True)
            # mixed-colour has even number of vertices, so next possible >=193 vertices is 194.
            if a<(194 if h==2 else 193)*c['scale']:break
if __name__=='__main__':main()
