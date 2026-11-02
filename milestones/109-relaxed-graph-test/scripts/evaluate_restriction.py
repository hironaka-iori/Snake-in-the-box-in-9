"""Recheck both profiles after the proved 01234 exclusion; finite graph only."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE/'scripts'));import check_graph as base
np=base.np;sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
start=time.monotonic();pins={}
def load(rel):
    p=ROOT/rel;pins[rel]=sha(p.read_bytes());return read(p)
new=load('milestones/109-relaxed-graph-test/data/NewRelaxed109-audit.json')
assert new['status']=='PASS_REFERENCE_RECOVERY_MODULE' and new['exit_code']==0
assert sha((HERE/'lean/NewRelaxed109.lean').read_bytes())==new['source_sha256']
graph='milestones/72-four-count-proof-closure/critical-current/'
meta=load(graph+'data/source-proved-model.json');gp=ROOT/(graph+'build/source-graph.npz')
pins[gp.relative_to(ROOT).as_posix()]=sha(gp.read_bytes())
with np.load(gp) as z:a={k:z[k] for k in z.files}
assert {k:sha(v.tobytes()) for k,v in a.items()}==meta['arrays_sha256']
ds=load('milestones/59-extended-share-window/extended/data/model.json')['extensions']
completed=load('milestones/73-countfree-share-catalogue/data/proved-model.json')
conditional=load('milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json')
audit=load('milestones/99-defined-potential-certificates/data/defined-potential-audit.json')
screen=load('milestones/109-relaxed-graph-test/data/candidate-graph-screen.json')
U,V,N=a['U'],a['V'],meta['states'];code=a['count_code'];enter=120*(code.astype(np.int64)%6+1)
assert len(U)==4947008 and N==1601856
allcodes=np.arange(46656,dtype=np.int64)
digits=np.stack([allcodes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
drop=np.zeros(len(U),dtype=bool)
for di,word in enumerate(ds):
    hit=np.zeros(46656,dtype=bool)
    for s in range(3):
        part=word[s+2:s+7]
        for rev in [False,True]:
            if base.canon(part[::-1] if rev else part)!=(0,1,2,3,4):continue
            cols=[s+j for j in ([3,2,0] if rev else [0,1,3])]
            hit|=(digits[:,cols[0]]<=1)&(digits[:,cols[1]]<=5)&(digits[:,cols[2]]<=2)
    lo,hi=np.searchsorted(a['direction'],[di,di+1]);drop[lo:hi]=hit[code[lo:hi]]
removed=np.flatnonzero(drop);assert len(removed)==2092
keys=((75*a['direction'][removed].astype(np.int64)+a['history'][removed])*46656+code[removed])
expected=next(r for r in screen['candidates'] if r['root']=='D01234A1542')
assert sha(keys.astype('<i8').tobytes())==expected['rejected_keys_sha256']
(HERE/'data/removed-edge-indices.json').write_text(json.dumps(removed.tolist())+'\n')
keep=~drop;u=U[keep];v=V[keep];shapes=[min(base.canon(w[-6:]),base.canon(w[-6:][::-1])) for w in ds]
cf={tuple(r['shape']):r['share'] for r in completed['countfree_floors']}
ff=cf|{(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
profiles=[]
for name,old,floors,P in [('completed',completed,cf,483),('conditional_floor18',conditional,ff,496)]:
    before=time.monotonic();floor=np.array([floors.get(s,0) for s in shapes],dtype=np.int64)
    full=np.maximum(a['weight'],enter+floor[a['direction']]);assert sha(full.tobytes())==old['weight_sha256']
    w=full[keep];cycle=[r['edge'] for r in old['cycle']]
    assert all(not drop[e] for e in cycle),'Old sharp cycle removed: recompute mean'
    assert all(V[x]==U[y] for x,y in zip(cycle,cycle[1:]+cycle[:1]))
    assert sum(int(full[e]) for e in cycle)==P*len(cycle)
    dist=np.zeros(N,dtype=np.int64)
    for iteration in range(1,201):
        nxt=dist.copy();np.minimum.at(nxt,v,dist[u]+w-P)
        if np.array_equal(nxt,dist):break
        dist=nxt
    else:raise AssertionError('No convergence in 200 iterations')
    assert np.all(P+dist[v]<=w+dist[u])
    pi=dist-dist.min();R=int(pi.max());buf=pi.astype('<i8').tobytes()
    filename=name+'-restricted-potential.i64.gz';(HERE/'data'/filename).write_bytes(gzip.compress(buf,mtime=0))
    bound=Fraction(1098960+8*P+R,4200+P)
    profiles.append(dict(profile=name,mean=P,range=R,previous_range=old['potential_range'],
        edges=len(u),removed_edges=len(removed),iterations=iteration,all_remaining_inequalities_checked=True,
        sharp_cycle_original_indices=cycle,sharp_cycle_survives=True,potential_file=filename,potential_sha256=sha(buf),
        remaining_weight_sha256=sha(w.tobytes()),comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,
        seconds=time.monotonic()-before))
    print(name,'mean',P,'range',R,'bound',bound,'iterations',iteration,flush=True)
assert all(sha((ROOT/p).read_bytes())==h for p,h in pins.items())
out=dict(status='EXACT_RESTRICTED_GRAPH_PROFILES',removed_edges=len(removed),remaining_edges=len(u),profiles=profiles,
    source_files_sha256=pins,removed_full_keys_sha256=sha(keys.astype('<i8').tobytes()),
    script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
    scope='The new exclusion has a checked actual-snake theorem. Both restricted finite profiles have exact potentials and surviving sharp cycles. A new complete restricted-graph certificate and assembly are not provided; no new numerical snake bound is claimed.')
(HERE/'data/restricted-profiles.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
