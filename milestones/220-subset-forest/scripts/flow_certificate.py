"""Save exact feasible flows certifying every induced-forest subset inequality."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.graph.python import max_flow
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
summary=[]
for root in [0,78]:
    model_path=H/'data'/f'forest-{root}'/'model.json';m=json.loads(model_path.read_bytes())
    cert_path=H/'data'/f'rational-{root}'/'primal-certificate.json';c=json.loads(cert_path.read_bytes())
    values=[Q(*q) for q in c['values']];D=lcm(*(q.denominator for q in values))
    z=[int(q*D) for q in values];assert all(Q(a,D)==b for a,b in zip(z,values))
    V=m['vertices'];pos={v:i for i,v in enumerate(V)};names={n:i for i,n in enumerate(m['variables'])};sink=len(V)
    arcs=[]
    for u,v in m['edges']:
        cap=z[names[f'y{u}_{v}']];arcs.extend([[pos[u],pos[v],cap],[pos[v],pos[u],cap]])
    for u in V:arcs.append([pos[u],sink,D if u==root else z[names[f'e{u}']] if f'e{u}' in names else 0])
    assert sum(a[2] for a in arcs)<2**62
    net=max_flow.SimpleMaxFlow()
    for u,v,cap in arcs:net.add_arc_with_capacity(u,v,cap)
    flows=[];violations=[];started=time.monotonic()
    for vertex in V:
        required=2*z[names[f'x{vertex}']]
        if required==0:
            flows.append({'source':vertex,'value':0,'nonzero_arcs':[]});continue
        assert net.solve(pos[vertex],sink)==net.OPTIMAL
        got=net.optimal_flow()
        if got<required:
            violations.append({'source':vertex,'required':required,'achieved':got,'subset':[V[i] for i in net.get_source_side_min_cut()]})
            continue
        nonzero=[];balance=[0]*(len(V)+1)
        for i,(u,v,cap) in enumerate(arcs):
            f=net.flow(i);assert 0<=f<=cap
            if f:nonzero.append([i,f])
            balance[u]+=f;balance[v]-=f
        assert balance[pos[vertex]]==got and balance[sink]==-got
        assert all(v==0 for i,v in enumerate(balance) if i not in [pos[vertex],sink])
        flows.append({'source':vertex,'value':got,'nonzero_arcs':nonzero})
    out=cert_path.with_name('forest-flow-certificate.json');assert not out.exists()
    save(out,{'model_sha256':sha(model_path),'primal_sha256':sha(cert_path),'source_sha256':sha(__file__),
        'scale':D,'vertices':V,'sink':sink,'arcs':arcs,'flows':flows,'violations':violations,
        'all_subset_inequalities':not violations,
        'argument':'Summing flow conservation over any subset containing its source and excluding the sink bounds its source supply by the outward cut capacity. Capacities are selected-edge values and endpoint masses. Required supply is2x_v.'})
    report={'root':root,'all_subset_inequalities':not violations,'flow_count':len(flows),'violations':len(violations),
        'scale':D,'seconds':time.monotonic()-started,'certificate_sha256':sha(out)}
    summary.append(report);save(H/'data/flow-summary.json',summary);print(json.dumps(report),flush=True)
