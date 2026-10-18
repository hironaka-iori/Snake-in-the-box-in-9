"""Exact sequence relaxation; executable evidence, not a Lean upper bound.

Enumerate extra forbidden sets in increasing cardinality, including reversal.
The first/last alpha belong to endpoints, so no forbidden internal triple may
involve them. Values >=8 compress to 8 (even) or 9 (odd), since all candidate
forbidden entries are <=7. This preserves parity and neighbor-of-one rules.
"""
import hashlib,itertools,json,pathlib,time
import numpy as np
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244/stage2'
survey=json.loads((OUT/'survey.json').read_text())
assert survey['status']=='COMPLETED_SOLVER_ONLY'
BASE={(2,2,2),(2,2,3),(3,2,2)}
canonical=[tuple(p) for p in survey['both_shapes_infeasible']]
candidates=[p for p in canonical if p not in BASE and p[::-1] not in BASE]
assert all(max(p)<=7 for p in canonical)
INF=10**6
alphabet=np.arange(1,10)
bad_adj=((alphabet[:,None]==1)&(alphabet[None,:]<4))|((alphabet[None,:]==1)&(alphabet[:,None]<4))
odd=np.array([i%2 for i in range(10)])
def rows(forbidden,maximum_internal=254):
    # State (previous, last, cost parity); zero is the initial sentinel.
    dp=np.full((10,10,2),INF,dtype=np.int64)
    dp[0,4,0]=4;dp[0,5,1]=5
    banned=np.zeros((10,10,10),dtype=bool)
    for p in forbidden:banned[p]=True
    answer=[]
    for n in range(maximum_internal+1):
        v=n+2
        t=min(int(dp[:,:,v%2].min())+4,int(dp[:,:,1-v%2].min())+5)
        e=18428-70*v-2*t
        answer.append(dict(vertices=v,edges=v-1,min_T=t,E=e,feasible=e>=0 and e%4==0))
        # Only after two internal vertices can a fully internal triple occur.
        expanded=np.broadcast_to(dp[:,:,None,:],(10,10,10,2))
        value=np.where(banned[:,:,:,None],INF,expanded).min(axis=0) if n>=2 else expanded.min(axis=0)
        value=value+np.arange(10)[None,:,None]
        value[:,1::2,:]=value[:,1::2,::-1]
        value[1:,1:,:]=np.where(bad_adj[:,:,None],INF,value[1:,1:,:])
        value[0,:,:]=INF;value[:,0,:]=INF
        dp=value
    return answer

# Exhaustive short paths independently check transitions and endpoint treatment.
for extra in [set(),{(4,1,4),(1,7,1)}]:
    forbidden=BASE|extra
    rr=rows(forbidden,3)
    for n in range(4):
        cost=[INF,INF]
        for inner in itertools.product(range(1,10),repeat=n):
            if any(inner[i:i+3] in forbidden for i in range(max(0,n-2))):continue
            for a,b in itertools.product((4,5),repeat=2):
                seq=(a,*inner,b)
                if any((x==1 and y<4) or (y==1 and x<4) for x,y in zip(seq,seq[1:])):continue
                t=sum(seq);cost[t%2]=min(cost[t%2],t)
        assert rr[n]['min_T']==cost[(n+2)%2],(n,extra,rr[n],cost)

result=dict(evidence='EXECUTABLE_DP_ONLY; new exclusions are SOLVER_ONLY',
    source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
    candidates=candidates,baseline_forbidden=sorted(BASE),alphabet=list(range(1,10)),
    endpoint_values=[4,5],internal_triples_only=True,short_exhaustive_check='PASSED',
    searched_subsets=0,minimum_sets={})
tick=time.monotonic()
for k in range(len(candidates)+1):
    for subset in itertools.combinations(candidates,k):
        f=BASE|set(subset)|{p[::-1] for p in subset}
        rr=rows(f)
        bound=max(r['edges'] for r in rr if r['feasible'])
        result['searched_subsets']+=1
        if not subset:
            assert bound==244,bound
            result['baseline_bound']=bound
        for target in [243,242]:
            key=str(target)
            if bound<=target and (key not in result['minimum_sets'] or result['minimum_sets'][key]['cardinality']==k):
                rec=result['minimum_sets'].setdefault(key,dict(cardinality=k,sets=[]))
                rec['sets'].append(dict(patterns=subset,relaxed_bound=bound))
    print('Completed cardinality',k,'subsets',result['searched_subsets'],flush=True)
    if all(str(t) in result['minimum_sets'] for t in [243,242]):break
result['elapsed_seconds']=time.monotonic()-tick
result['all_candidate_bound']=max(r['edges'] for r in rows(BASE|set(candidates)|{p[::-1] for p in candidates}) if r['feasible'])
path=OUT/'minimal-patterns.json';path.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps(result,indent=2))
