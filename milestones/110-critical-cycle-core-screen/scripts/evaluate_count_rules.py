"""Exact profiles after one or seven proposed plain-count exclusions."""
from pathlib import Path
from fractions import Fraction
import argparse,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'milestones/42-six-count-state-model/scripts'),str(ROOT/'milestones/51-exact-bucket-pressure/scripts')]
import analyze_share
np=analyze_share.np;alg,algsha=analyze_share.algorithms();sha=lambda b:hashlib.sha256(b).hexdigest();pins={}
def read(rel):
    raw=(ROOT/rel).read_bytes();pins[rel]=sha(raw);return json.loads(raw)
def canon(word):
    names={};return tuple(names.setdefault(int(x),len(names)) for x in word)
def enc(xs):
    n=0
    for x in xs:n=6*n+x-1
    return n
ap=argparse.ArgumentParser();ap.add_argument('--all',action='store_true');args=ap.parse_args()
start=time.monotonic();folder=HERE/('data/count-profiles-all' if args.all else 'data/count-profiles-one');folder.mkdir(exist_ok=True)
assert not (folder/'results.json').exists()
rules=[]
for path in sorted((HERE/'data/plain-probes').glob('*.json')):
    row=read(path.relative_to(ROOT).as_posix())
    if args.all or row['edge']==3534483:
        assert row['status']=='UNSAT_UNCERTIFIED' and not row['cycle_cuts']
        rules.append(dict(directions=row['directions'],counts=row['counts'],source=path.relative_to(ROOT).as_posix()))
graph='milestones/72-four-count-proof-closure/critical-current/'
meta=read(graph+'data/source-proved-model.json');gp=ROOT/(graph+'build/source-graph.npz');pins[gp.relative_to(ROOT).as_posix()]=sha(gp.read_bytes())
with np.load(gp) as z:a={k:z[k] for k in z.files}
assert {k:sha(v.tobytes()) for k,v in a.items()}==meta['arrays_sha256']
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
completed=read('milestones/73-countfree-share-catalogue/data/proved-model.json')
conditional=read('milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json')
prior=read('milestones/109-relaxed-graph-test/data/removed-edge-indices.json')
drop=np.zeros(len(a['U']),dtype=bool);drop[prior]=True;code=a['count_code']
for rule in rules:
    found=np.zeros(len(drop),dtype=bool)
    for di,word in enumerate(ds):
        lo,hi=np.searchsorted(a['direction'],[di,di+1])
        for s in range(2):
            part=word[s+2:s+8];target=tuple(rule['directions']);c=code[lo:hi]//6**(1-s)%7776
            f,b=canon(part),canon(part[::-1])
            found[lo:hi]|=((f==target)&(c==enc(rule['counts'])))|((b==target)&(c==enc(rule['counts'][::-1])))
    rule['matches_full_graph']=int(found.sum());rule['additional_to_prior']=int(np.count_nonzero(found&~drop));drop|=found
removed=np.flatnonzero(drop);(folder/'removed-indices.json').write_text(json.dumps(removed.tolist())+'\n')
keep=~drop;original=np.flatnonzero(keep);U,V,N=a['U'][keep],a['V'][keep],meta['states']
cf={tuple(r['shape']):r['share'] for r in completed['countfree_floors']}
ff=cf|{(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
shapes=[min(canon(w[-6:]),canon(w[-6:][::-1])) for w in ds]
pool=np.flatnonzero(alg['prune'](N,U,V));active=np.unique(np.concatenate([U[pool],V[pool]]))
index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active));profiles=[]
for name,old,floors in [('completed',completed,cf),('conditional_floor18',conditional,ff)]:
    before=time.monotonic();floor=np.array([floors.get(s,0) for s in shapes],dtype=np.int64)
    full=np.maximum(a['weight'],120*(code.astype(np.int64)%6+1)+floor[a['direction']]);assert sha(full.tobytes())==old['weight_sha256']
    W=full[keep];_,cy=alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400)
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
    cycle=[dict(edge=int(original[e]),u=int(U[e]),v=int(V[e]),direction=int(a['direction'][original[e]]),history=int(a['history'][original[e]]),
        count_code=int(a['count_code'][original[e]]),weight=int(W[e])) for e in ci]
    profiles.append(dict(profile=name,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,
        weight_sha256=sha(W.tobytes()),potential_file=filename,potential_sha256=sha(buf),all_edge_inequalities_checked=True,
        iterations=iteration,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,seconds=time.monotonic()-before))
    print(name,'mean',mu,'range',Fraction(R,d),'comparison',bound,'integer',bound.numerator//bound.denominator,flush=True)
assert all(sha((ROOT/p).read_bytes())==h for p,h in pins.items())
out=dict(status='EXACT_FINITE_PROFILES_UNDER_PROPOSED_COUNT_EXCLUSIONS',rules=rules,profiles=profiles,states=N,edges=len(U),
    removed=len(removed),additional_removed=len(removed)-len(prior),source_files_sha256=pins,algorithm_sha256=algsha,
    script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
    scope='Exact finite graph experiment. Proof status of each count exclusion is separate; native UNSAT alone does not establish it. Full graph prerequisites and Lean potential assembly remain pending. No new numerical bound.')
(folder/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print('Additional excluded keys:',out['additional_removed'],flush=True)
