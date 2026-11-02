"""Check the intersection of the two111 graph experiments using saved exact potentials."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins={}
def read(p):pins[p.relative_to(ROOT).as_posix()]=sha(p);return json.loads(p.read_text())
def canon(word):
    names={};return tuple(names.setdefault(int(x),len(names)) for x in word)
mid=read(HERE/'data/middle325-profiles/results.json');sumr=read(HERE/'data/sum22-profiles/results.json')
old=set(read(ROOT/'milestones/110-critical-cycle-core-screen/data/count-profiles-one/removed-indices.json'))
mi=set(read(HERE/'data/middle325-profiles/removed-indices.json'));su=set(read(HERE/'data/sum22-profiles/removed-indices.json'))
assert old<=mi and old<=su and not (mi-old)&(su-old)
gp=ROOT/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz';pins[gp.relative_to(ROOT).as_posix()]=sha(gp)
with np.load(gp) as z:a={k:z[k] for k in z.files}
ds=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
completed=read(ROOT/'milestones/73-countfree-share-catalogue/data/proved-model.json')
conditional=read(ROOT/'milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json')
drop=np.zeros(len(a['U']),dtype=bool);drop[list(mi|su)]=True;keep=~drop
code=a['count_code'];digits=np.stack([code//6**j%6+1 for j in range(5,-1,-1)],axis=1);bonus=np.zeros(len(code),dtype=np.int64)
for di,word in enumerate(ds):
    if canon(word[-6:])!=(0,1,2,3,4,0) and canon(word[-6:][::-1])!=(0,1,2,3,4,0):continue
    lo,hi=np.searchsorted(a['direction'],[di,di+1]);v=digits[lo:hi]
    bonus[lo:hi]=30*np.where(v[:,3]<=2,np.maximum(0,22-v[:,[1,2,4,5]].sum(axis=1)),0)
cf={tuple(r['shape']):r['share'] for r in completed['countfree_floors']};ff=cf|{(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
shapes=[min(canon(w[-6:]),canon(w[-6:][::-1])) for w in ds];results=[]
for profile,model,floors in zip(sumr['profiles'],[completed,conditional],[cf,ff]):
    floor=np.array([floors.get(s,0) for s in shapes],dtype=np.int64);base=np.maximum(a['weight'],120*(code.astype(np.int64)%6+1)+floor[a['direction']])
    assert hashlib.sha256(base.tobytes()).hexdigest()==model['weight_sha256'];full=base+bonus
    pk=HERE/'data/sum22-profiles'/profile['potential_file'];pins[pk.relative_to(ROOT).as_posix()]=sha(pk)
    raw=gzip.decompress(pk.read_bytes());assert hashlib.sha256(raw).hexdigest()==profile['potential_sha256']
    pi=np.frombuffer(raw,dtype='<i8');p,d=profile['p'],profile['d']
    assert np.all(p+pi[a['V'][keep]]<=d*full[keep]+pi[a['U'][keep]])
    cycle=[r['edge'] for r in profile['cycle']];assert all(e not in mi|su for e in cycle)
    assert d*sum(int(full[e]) for e in cycle)==p*len(cycle) and all(bonus[e]==0 for e in cycle)
    assert all(np.all(digits[e]<6) for e in cycle)
    results.append(dict(profile=profile['profile'],mean=profile['mean'],range=profile['range'],comparison=profile['comparison_integer_bound'],
        all_edge_inequalities_checked=True,attaining_cycle=cycle,all_cycle_symbols_below6=True))
assert all(sha(ROOT/p)==h for p,h in pins.items())
out=dict(status='PASS_COMBINED_CONDITIONAL_GRAPH_EXPERIMENT',previous_exclusions=len(old),new_middle_exclusions=len(mi-old),new_sum_exclusions=len(su-old),
    new_exclusion_sets_disjoint=True,total_exclusions=len(mi|su),remaining_edges=int(keep.sum()),profiles=results,
    source_files_sha256=pins,script_sha256=sha(Path(__file__)),scope='Combination remains conditional on the unproved sum inequality and excess budget. Exact old potentials and surviving cycles establish unchanged means and comparisons on the intersection. No new global bound.')
(HERE/'data/combined-experiment.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='source_files_sha256'},indent=2))
