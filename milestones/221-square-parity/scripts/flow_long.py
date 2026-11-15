"""Construct exact feasible endpoint flows with arbitrary integer capacities."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
from collections import deque
import hashlib,json,time
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
def feasible_flow(arcs,n,source,sink,demand):
    adj=[[] for _ in range(n)];locations=[]
    for u,v,c in arcs:
        assert u!=v and c>=0
        a=len(adj[u]);b=len(adj[v]);locations.append((u,a))
        adj[u].append([v,c,b]);adj[v].append([u,0,a])
    total=0
    while total<demand:
        level=[-1]*n;level[source]=0;todo=deque([source])
        while todo:
            u=todo.popleft()
            for v,c,r in adj[u]:
                if c>0 and level[v]<0:level[v]=level[u]+1;todo.append(v)
        if level[sink]<0:break
        it=[0]*n
        def send(u,limit):
            if u==sink:return limit
            while it[u]<len(adj[u]):
                v,c,r=adj[u][it[u]]
                if c>0 and level[v]==level[u]+1:
                    f=send(v,min(limit,c))
                    if f:
                        adj[u][it[u]][1]-=f;adj[v][r][1]+=f;return f
                it[u]+=1
            return 0
        while total<demand:
            f=send(source,demand-total)
            if f==0:break
            total+=f
    return total,[arcs[i][2]-adj[u][j][1] for i,(u,j) in enumerate(locations)]
summary=[]
for root in [0,78]:
    mp=H/'data'/f'long-{root}'/'model.json';m=json.loads(mp.read_bytes())
    pp=H/'data'/f'rational-long-{root}'/'primal-certificate.json';p=json.loads(pp.read_bytes())
    q=[Q(*x) for x in p['values']];D=lcm(*(x.denominator for x in q));z=[int(x*D) for x in q]
    assert all(Q(v,D)==x for v,x in zip(z,q))
    V=m['vertices'];pos={v:i for i,v in enumerate(V)};names={v:i for i,v in enumerate(m['variables'])};sink=len(V)
    arcs=[]
    for u,v in m['edges']:
        c=z[names[f'y{u}_{v}']];arcs.extend([[pos[u],pos[v],c],[pos[v],pos[u],c]])
    for v in V:arcs.append([pos[v],sink,D if v==root else z[names[f'e{v}']] if f'e{v}' in names else 0])
    flows=[];violations=[];started=time.monotonic()
    for v in V:
        required=2*z[names[f'x{v}']];total,f=feasible_flow(arcs,len(V)+1,pos[v],sink,required)
        balance=[0]*(len(V)+1)
        for (u,w,c),value in zip(arcs,f):
            assert 0<=value<=c;balance[u]+=value;balance[w]-=value
        assert balance[pos[v]]==total and balance[sink]==-total
        assert all(b==0 for i,b in enumerate(balance) if i not in [pos[v],sink])
        if total<required:violations.append({'source':v,'required':required,'achieved':total})
        flows.append({'source':v,'value':total,'nonzero_arcs':[[i,a] for i,a in enumerate(f) if a]})
    out=pp.with_name('forest-flow-certificate.json');assert not out.exists()
    save(out,{'model_sha256':sha(mp),'primal_sha256':sha(pp),'source_sha256':sha(__file__),'scale':D,
        'vertices':V,'sink':sink,'arcs':arcs,'flows':flows,'violations':violations,'all_subset_inequalities':not violations,
        'argument':'A separate feasible flow of supply2x_v bounds every cut containing source v. Exact capacities and conservation suffice; optimizer optimality is unnecessary.'})
    row={'root':root,'scale':D,'scale_bits':D.bit_length(),'flow_count':len(flows),'violations':len(violations),
        'all_subset_inequalities':not violations,'seconds':time.monotonic()-started,'certificate_sha256':sha(out)}
    summary.append(row);save(H/'data/flow-long-summary.json',summary);print(json.dumps(row),flush=True)
