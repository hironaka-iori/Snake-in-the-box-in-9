"""Evaluate a conditional outer-count inequality with correctly separated excess credit."""
from pathlib import Path
from fractions import Fraction
import argparse,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'milestones/42-six-count-state-model/scripts'),str(ROOT/'milestones/51-exact-bucket-pressure/scripts')]
import analyze_share
np=analyze_share.np;alg,algsha=analyze_share.algorithms();sha=lambda b:hashlib.sha256(b).hexdigest();pins={}
def read(rel):
    b=(ROOT/rel).read_bytes();pins[rel]=sha(b);return json.loads(b)
def canon(word):
    names={};return tuple(names.setdefault(int(x),len(names)) for x in word)
ap=argparse.ArgumentParser();ap.add_argument('--lower',type=int,default=22);args=ap.parse_args();L=args.lower
probe=read(f'milestones/111-critical-count-intervals/data/probes/outer-sum{L-1}.json');assert probe['status']=='UNSAT_UNCERTIFIED'
folder=HERE/f'data/sum{L}-profiles';folder.mkdir(exist_ok=True);assert not (folder/'results.json').exists()
start=time.monotonic();graph='milestones/72-four-count-proof-closure/critical-current/'
meta=read(graph+'data/source-proved-model.json');gp=ROOT/(graph+'build/source-graph.npz');pins[gp.relative_to(ROOT).as_posix()]=sha(gp.read_bytes())
with np.load(gp) as z:a={k:z[k] for k in z.files}
assert {k:sha(v.tobytes()) for k,v in a.items()}==meta['arrays_sha256']
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
completed=read('milestones/73-countfree-share-catalogue/data/proved-model.json')
conditional=read('milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json')
prior=read('milestones/110-critical-cycle-core-screen/data/count-profiles-one/removed-indices.json')
drop=np.zeros(len(a['U']),dtype=bool);drop[prior]=True;code=a['count_code'];bonus=np.zeros(len(code),dtype=np.int64)
digits=np.stack([code//6**j%6+1 for j in range(5,-1,-1)],axis=1)
for di,word in enumerate(ds):
    lo,hi=np.searchsorted(a['direction'],[di,di+1])
    for s in range(2):
        part=word[s+2:s+8]
        if canon(part)!=(0,1,2,3,4,0) and canon(part[::-1])!=(0,1,2,3,4,0):continue
        values=digits[lo:hi];outer=values[:,[s,s+1,s+3,s+4]]
        demand=np.where(values[:,s+2]<=2,np.maximum(0,L-outer.sum(axis=1)),0)
        drop[lo:hi]|=(demand>0)&np.all(outer<6,axis=1)
        if s==1:bonus[lo:hi]=30*demand
removed=np.flatnonzero(drop);(folder/'removed-indices.json').write_text(json.dumps(removed.tolist())+'\n')
keep=~drop;original=np.flatnonzero(keep);U,V,N=a['U'][keep],a['V'][keep],meta['states']
cf={tuple(r['shape']):r['share'] for r in completed['countfree_floors']}
ff=cf|{(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
shapes=[min(canon(w[-6:]),canon(w[-6:][::-1])) for w in ds]
pool=np.flatnonzero(alg['prune'](N,U,V));active=np.unique(np.concatenate([U[pool],V[pool]]))
index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active));profiles=[]
for name,old,floors in [('completed',completed,cf),('conditional_floor18',conditional,ff)]:
    before=time.monotonic();floor=np.array([floors.get(s,0) for s in shapes],dtype=np.int64)
    baseline=np.maximum(a['weight'],120*(code.astype(np.int64)%6+1)+floor[a['direction']]);assert sha(baseline.tobytes())==old['weight_sha256']
    W=(baseline+bonus)[keep];_,cy=alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400)
    ci=pool[np.asarray(cy)];mu=Fraction(int(W[ci].sum()),len(ci));p,d=mu.numerator,mu.denominator
    assert all(V[ci[i]]==U[ci[(i+1)%len(ci)]] for i in range(len(ci)))
    dist=np.zeros(N,dtype=np.int64)
    for iteration in range(1,1501):
        nxt=dist.copy();np.minimum.at(nxt,V,dist[U]+d*W-p)
        if np.array_equal(nxt,dist):break
        dist=nxt
    else:raise AssertionError('Potential did not converge')
    assert np.all(p+dist[V]<=d*W+dist[U]);pi=dist-dist.min();R=int(pi.max())
    buf=pi.astype('<i8').tobytes();filename=name+'-potential.i64.gz';(folder/filename).write_bytes(gzip.compress(buf,mtime=0))
    bound=Fraction(1098960*d+8*p+R,4200*d+p)
    cycle=[dict(edge=int(original[e]),direction=int(a['direction'][original[e]]),history=int(a['history'][original[e]]),
        count_code=int(a['count_code'][original[e]]),u=int(U[e]),v=int(V[e]),weight=int(W[e]),bonus=int(bonus[original[e]])) for e in ci]
    profiles.append(dict(profile=name,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,
        weight_sha256=sha(W.tobytes()),potential_file=filename,potential_sha256=sha(buf),all_edge_inequalities_checked=True,
        iterations=iteration,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,seconds=time.monotonic()-before))
    print(name,'mean',mu,'range',Fraction(R,d),'comparison',bound,'integer',bound.numerator//bound.denominator,flush=True)
assert all(sha((ROOT/p).read_bytes())==h for p,h in pins.items())
out=dict(status='EXACT_FINITE_PROFILES_WITH_UNPROVED_OUTER_SUM_INEQUALITY',outer_sum_lower=L,centre_upper=2,directions=[0,1,2,3,4,0],
    profiles=profiles,states=N,edges=len(U),additional_removed=len(removed)-len(prior),bonus_edges=int(np.count_nonzero(bonus[keep])),
    bonus_coefficient=30,source_files_sha256=pins,algorithm_sha256=algsha,script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
    scope='Conditional native experiment only. Local sum inequality and its count-excess budget are not yet checked. The bonus uses only the suffix and four fixed positions, overlap at most4. Counts with no saturated symbol give exclusions at both offsets. Existing graph prerequisites remain; no new global bound.')
(folder/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print('Additional removed',out['additional_removed'],'bonus edges',out['bonus_edges'],flush=True)
