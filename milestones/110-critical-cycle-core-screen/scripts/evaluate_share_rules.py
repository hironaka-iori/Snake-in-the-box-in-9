"""Exact finite profiles under explicitly unproved cycle-window share bounds."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'milestones/42-six-count-state-model/scripts'),str(ROOT/'milestones/51-exact-bucket-pressure/scripts')]
import analyze_share
np=analyze_share.np;alg,algsha=analyze_share.algorithms()
sha=lambda b:hashlib.sha256(b).hexdigest();pins={}
def read(rel):
    p=ROOT/rel;raw=p.read_bytes();pins[rel]=sha(raw);return json.loads(raw)
def canon(word):
    names={};return tuple(names.setdefault(int(x),len(names)) for x in word)
def enc(xs):
    n=0
    for x in xs:n=6*n+x-1
    return n
start=time.monotonic();outdir=HERE/'data/share-profiles';outdir.mkdir(exist_ok=True)
assert not (outdir/'results.json').exists(),'Save a new attempt instead of overwriting results.'
rules={}
for p in sorted((HERE/'data/share-probes').glob('*.json')):
    d=read(p.relative_to(ROOT).as_posix())
    if d['status']!='UNSAT_UNCERTIFIED':continue
    key=(tuple(d['directions']),tuple(d['counts']))
    if key not in rules or rules[key]['share']<d['cap']+1:
        rules[key]=dict(directions=d['directions'],counts=d['counts'],share=d['cap']+1,
                       probe=p.relative_to(ROOT).as_posix(),status='UNPROVED_LOCAL_SHARE_ASSUMPTION')
assert len(rules)>=3
graph='milestones/72-four-count-proof-closure/critical-current/'
meta=read(graph+'data/source-proved-model.json');gp=ROOT/(graph+'build/source-graph.npz');pins[gp.relative_to(ROOT).as_posix()]=sha(gp.read_bytes())
with np.load(gp) as z:a={k:z[k] for k in z.files}
assert {k:sha(v.tobytes()) for k,v in a.items()}==meta['arrays_sha256']
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
completed=read('milestones/73-countfree-share-catalogue/data/proved-model.json')
conditional=read('milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json')
removed=read('milestones/109-relaxed-graph-test/data/removed-edge-indices.json')
keep=np.ones(len(a['U']),dtype=bool);keep[removed]=False;original=np.flatnonzero(keep)
U,V,N=a['U'][keep],a['V'][keep],meta['states'];code=a['count_code'];enter=120*(code.astype(np.int64)%6+1)
credit=np.zeros(len(code),dtype=np.int64);hits=[]
for rule in rules.values():
    changed=0
    for di,word in enumerate(ds):
        f,b=canon(word[-6:]),canon(word[-6:][::-1]);target=tuple(rule['directions'])
        if f!=target and b!=target:continue
        lo,hi=np.searchsorted(a['direction'],[di,di+1]);c=code[lo:hi]%7776
        hit=((f==target)&(c==enc(rule['counts'])))|((b==target)&(c==enc(rule['counts'][::-1])))
        credit[lo:hi][hit]=np.maximum(credit[lo:hi][hit],rule['share']);changed+=int(hit.sum())
    hits.append(dict(rule,matching_full_keys=changed))
cf={tuple(r['shape']):r['share'] for r in completed['countfree_floors']}
ff=cf|{(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
shapes=[min(canon(w[-6:]),canon(w[-6:][::-1])) for w in ds]
pool=np.flatnonzero(alg['prune'](N,U,V));active=np.unique(np.concatenate([U[pool],V[pool]]))
index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active));profiles=[]
for name,old,floors in [('completed_plus_new',completed,cf),('conditional_plus_new',conditional,ff)]:
    before=time.monotonic();floor=np.array([floors.get(s,0) for s in shapes],dtype=np.int64)
    baseline=np.maximum(a['weight'],enter+floor[a['direction']]);assert sha(baseline.tobytes())==old['weight_sha256']
    full=np.maximum(baseline,enter+credit);W=full[keep]
    _,cy=alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400)
    ci=pool[np.asarray(cy)];mu=Fraction(int(W[ci].sum()),len(ci));p,d=mu.numerator,mu.denominator
    assert all(V[ci[i]]==U[ci[(i+1)%len(ci)]] for i in range(len(ci)))
    dist=np.zeros(N,dtype=np.int64)
    for iteration in range(1,1501):
        nxt=dist.copy();np.minimum.at(nxt,V,dist[U]+d*W-p)
        if np.array_equal(nxt,dist):break
        dist=nxt
    else:raise AssertionError('Potential did not converge')
    assert np.all(p+dist[V]<=d*W+dist[U]);pi=dist-dist.min();R=int(pi.max())
    buf=pi.astype('<i8').tobytes();filename=name+'-potential.i64.gz';(outdir/filename).write_bytes(gzip.compress(buf,mtime=0))
    bound=Fraction(1098960*d+8*p+R,4200*d+p)
    cycle=[dict(edge=int(original[e]),u=int(U[e]),v=int(V[e]),direction=int(a['direction'][original[e]]),history=int(a['history'][original[e]]),
        count_code=int(a['count_code'][original[e]]),weight=int(W[e])) for e in ci]
    result=dict(profile=name,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),
        changed_edges=int(np.count_nonzero(full[keep]>baseline[keep])),cycle=cycle,weight_sha256=sha(W.tobytes()),
        potential_file=filename,potential_sha256=sha(buf),all_edge_inequalities_checked=True,iterations=iteration,
        comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,seconds=time.monotonic()-before)
    profiles.append(result);print(name,'mean',mu,'range',Fraction(R,d),'comparison',bound,'integer',result['comparison_integer_bound'],flush=True)
assert all(sha((ROOT/p).read_bytes())==h for p,h in pins.items())
out=dict(status='EXACT_FINITE_PROFILES_WITH_UNPROVED_NEW_SHARE_RULES',rules=hits,profiles=profiles,
    states=N,edges=len(U),source_files_sha256=pins,algorithm_sha256=algsha,script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
    scope='Exact finite-graph calculation under the listed new local share assumptions. Native UNSAT probes do not prove those assumptions. Existing reference and profile prerequisites, full graph interpretation and kernel potential certificates remain separate. No new global bound.')
(outdir/'results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
