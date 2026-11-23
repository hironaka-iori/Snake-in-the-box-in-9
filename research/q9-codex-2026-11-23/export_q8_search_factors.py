"""Export local primal options and integer dual scores for conditioned search."""
import json, sys
from verify_q8_free_layer_dual import incident_choices, is_forest

def emit(r):
    c=r['certificate']; arm=c['arm']; root=arm[0]; scale=c['scale']; fee=c['end_weight']
    parity_fee=c.get('parity_weight',0)
    constant=fee+parity_fee*int(c['end_parity']==0)
    free=set(range(256))-set(arm[1:])
    ds={sum(1<<d for d in a):[1<<d for d in a] for a in c['directions']}
    w={(f,v,sum(d for j,d in enumerate(ds[f]) if local>>j&1)):cost for f,v,local,cost in c['matching_weights']}
    choices={v:list(incident_choices(v,root,c['end_parity'],free)) for v in free}
    groups=[]
    for v in sorted(free):
        adj=sorted(u for u in free if (u^v).bit_count()==1)
        group=[v,*adj]; limit=(1<<len(group))-1
        opts=[] if v==root else [(0,1,0)]
        for z in choices[v]:
            if z is None:continue
            on=1+sum(1<<i for i,u in enumerate(adj,1) if z&(u^v))
            value=scale-parity_fee*(1 if (v^root).bit_count()%2==0 else -1)-(fee if v!=root and z.bit_count()==1 else 0)+sum(w.get((f,v,z&f),0) for f in ds)
            opts.append((on,limit^on,value))
        groups.append((group,opts))
    for f,dirs in ds.items():
        for base in range(256):
            if base&f:continue
            g=sorted(v for v in free if v&~f==base)
            if not g:continue
            limit=(1<<len(g))-1;opts=[]
            states={v:{z&f for z in choices[v] if z is not None} for v in g}
            for on in range(limit+1):
                pts={v for i,v in enumerate(g) if on>>i&1}
                if root in g and root not in pts:continue
                deg={v:sum(d for d in dirs if v^d in pts) for v in pts}
                if any(z not in states[v] for v,z in deg.items()) or not is_forest(pts,dirs):continue
                opts.append((on,limit^on,-sum(w.get((f,v,z),0) for v,z in deg.items())))
            groups.append((g,opts))
    ub=constant+sum(max(s for _,_,s in opts) for _,opts in groups)
    assert ub==c['integer_numerator']
    print(r['index'],r['target_vertices'],root,scale,constant,ub,len(arm),*arm,len(groups))
    for g,opts in groups:
        print(len(g),*g,len(opts))
        for a,b,s in sorted(opts,key=lambda t:-t[2]):print(a,b,s)

if __name__=='__main__':
    ids=set(map(int,sys.argv[2:]))
    for line in open(sys.argv[1]):
        r=json.loads(line)
        if not ids or r['index'] in ids:emit(r)
