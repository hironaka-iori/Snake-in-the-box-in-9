"""Extract cycle/path certificates for the three exact saved finite models."""
from pathlib import Path
from fractions import Fraction
import datetime,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
OLD=ROOT/'milestones/72-four-count-proof-closure/critical-current'
CAT=ROOT/'milestones/73-countfree-share-catalogue';P83=ROOT/'milestones/83-012034-share-certificate'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
source=read(OLD/'data/source-proved-model.json')
with np.load(OLD/'build/source-graph.npz') as z:arrays={k:z[k] for k in z.files}
for k,h in source['arrays_sha256'].items():assert sha(arrays[k].tobytes())==h,k
U,V=arrays['U'],arrays['V'];N=source['states']
extensions_path=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
extensions=read(extensions_path)['extensions']
dag_path=ROOT/'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
dag=json.loads(gzip.decompress(dag_path.read_bytes()));blocks=dict(dag['blocks']);nodes=dag['nodes'];roots=dag['roots']
assert len(extensions)==505 and len(blocks)==791 and len(roots)==127

def canon(word):
    d={};return tuple(d.setdefault(x,len(d)) for x in word)

def make_weights(model):
    floors={tuple(r['shape']):r['share'] for r in model['countfree_floors']}
    by_direction=np.asarray([floors.get(min(canon(ds[-6:]),canon(ds[-6:][::-1])),0) for ds in extensions],dtype=np.int64)
    entering=120*(arrays['count_code'].astype(np.int64)%6+1)
    assert np.all(arrays['weight']>=entering)
    W=np.maximum(arrays['weight'].astype(np.int64),entering+by_direction[arrays['direction']])
    assert sha(W.tobytes())==model['weight_sha256']
    return W

def accepted(di,q,code):
    assert 0<=di<505 and 0<=q<75 and 0<=code<46656
    cls=blocks[75*di+q];node=roots[cls]
    for j in range(5,-1,-1):
        symbol=code//(6**j)%6+1
        if node>=2:node=nodes[node-2][symbol]
    assert node==1,(di,q,code,cls)
    return cls

def tight_path(W,pi,p,d,R):
    slack=d*W+pi[U]-pi[V]-p;assert int(slack.min())>=0
    tight=slack==0;del slack
    frontier=pi==R;seen=frontier.copy();pred=np.full(N,-1,dtype=np.int64)
    rounds=[];end=None
    for depth in range(1,1501):
        edges=np.flatnonzero(tight & frontier[U] & ~seen[V])
        assert len(edges),'No tight path from the maximum to the minimum'
        targets,first=np.unique(V[edges],return_index=True)
        pred[targets]=edges[first];seen[targets]=True
        rounds.append(dict(depth=depth,new_vertices=len(targets)))
        goals=targets[pi[targets]==0]
        if len(goals):end=int(goals[0]);break
        frontier=np.zeros(N,dtype=bool);frontier[targets]=True
    assert end is not None
    reverse=[];v=end
    while pred[v]>=0:
        e=int(pred[v]);assert int(V[e])==v
        reverse.append(e);v=int(U[e])
    path=list(reversed(reverse))
    assert len(path)==len(rounds) and int(pi[v])==R and int(pi[end])==0
    assert p*len(path)-d*sum(int(W[e]) for e in path)==R
    return path,rounds,int(tight.sum())

def edge_record(e,W,pi):
    di,q,c=(int(arrays[k][e]) for k in ['direction','history','count_code'])
    cls=accepted(di,q,c)
    return dict(edge=e,direction=di,history=q,count_code=c,diagram_class=cls,
                u=int(U[e]),v=int(V[e]),weight=int(W[e]),
                source_potential=int(pi[U[e]]),target_potential=int(pi[V[e]]))

tag='countfree16-all-except012034x20-except012310x12'
specs=[('completed',CAT/'data/proved-model.json',CAT/'data/proved-potential.i64.gz',None),
       ('additional012034',P83/'data/assumed-012034x20-model.json',P83/'data/assumed-012034x20-potential.i64.gz',None),
       ('full-conditional',OLD/f'data/{tag}-analysis.json',OLD/f'data/{tag}-potential.i64.gz',OLD/f'data/{tag}-model.json')]
summaries=[]
for label,mp,pp,extra in specs:
    start=time.monotonic();model=read(mp)
    if extra is None:
        W=make_weights(model);mu=Fraction(model['mean']);input_weights=model['weight_sha256']
    else:
        metadata=read(extra)
        with np.load(OLD/f'build/{tag}-graph.npz') as z:W=z['weight']
        assert sha(W.tobytes())==metadata['arrays_sha256']['weight']
        assert all(metadata['arrays_sha256'][k]==source['arrays_sha256'][k] for k in source['arrays_sha256'] if k!='weight')
        mu=Fraction(model['integer_mean']);input_weights=metadata['arrays_sha256']['weight']
    p,d=mu.numerator,mu.denominator
    raw=gzip.decompress(pp.read_bytes());assert sha(raw)==model['potential_sha256']
    pi=np.frombuffer(raw,dtype='<i8');R=int(model['potential_range'])
    assert len(pi)==N and int(pi.min())==0 and int(pi.max())==R
    path,rounds,tight_count=tight_path(W,pi,p,d,R)
    cycle=[int(r['edge']) for r in model['cycle']]
    assert cycle and all(int(V[cycle[i]])==int(U[cycle[(i+1)%len(cycle)]]) for i in range(len(cycle)))
    assert d*sum(int(W[e]) for e in cycle)==p*len(cycle)
    for r,e in zip(model['cycle'],cycle):
        assert r['u']==int(U[e]) and r['v']==int(V[e]) and r['weight']==int(W[e])
    total=sum(int(W[e]) for e in path);k=len(path)
    bound=Fraction(1098960*d+8*p+R,4200*d+p)
    assert Fraction(k+8)<=bound
    inputs=[mp,pp,dag_path,extensions_path,OLD/'data/source-proved-model.json']+([extra] if extra else [])
    result=dict(status='EXACT_FINITE_CYCLE_PATH_CERTIFICATE',model=label,mean=str(mu),denominator=d,
        potential_range_scaled=R,potential_range=str(Fraction(R,d)),path_edges=k,path_weight=total,
        path_deficit_scaled=p*k-d*total,cycle_edges=len(cycle),cycle_weight=sum(int(W[e]) for e in cycle),
        shortest_tight_path=True,bfs_rounds=rounds,tight_edges=tight_count,
        path=[edge_record(e,W,pi) for e in path],cycle=[edge_record(e,W,pi) for e in cycle],
        all_array_edge_inequalities_checked=True,witness_keys_accepted_by_diagram=True,
        comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,
        joint_slope_range_condition=True,joint_condition_margin=str(bound-(k+8)),
        arrays_sha256=source['arrays_sha256'],weight_sha256=input_weights,potential_sha256=sha(raw),
        input_sha256={str(x.relative_to(ROOT)):sha(x.read_bytes()) for x in inputs},
        script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
        scope='Exact Python checks on the pinned finite weighted model. Witness keys are accepted by the defined diagram. General optimization logic and concrete membership/weights are not claimed kernel-certified here. Local-share, reference and arbitrary-snake obligations remain.')
    (HERE/'data'/f'{label}-range-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    summaries.append({k:result[k] for k in ['model','mean','potential_range_scaled','path_edges','path_weight','cycle_edges','comparison_bound','joint_condition_margin','seconds']})
    print(summaries[-1],flush=True)
out=dict(status='EXTRACTED_THREE_FINITE_MODEL_CERTIFICATES',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),models=summaries,
         previous_goal_turn='progress',scope='No improved numerical snake bound and no claim that the abstract graph is realizable by one snake.')
(HERE/'data/range-certificate-summary.json').write_text(json.dumps(out,indent=2)+'\n')
