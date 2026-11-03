"""Guarded six-count sum credit using the existing last-five24budget."""
from pathlib import Path
from fractions import Fraction
import argparse, gzip, hashlib, json, sys, time
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path[:0] = [str(ROOT / 'milestones/42-six-count-state-model/scripts'), str(ROOT / 'milestones/51-exact-bucket-pressure/scripts')]
import analyze_share
np = analyze_share.np
alg, algsha = analyze_share.algorithms()
sha = lambda b: hashlib.sha256(b).hexdigest()
pins = {}
def read(rel):
    raw = (ROOT / rel).read_bytes()
    pins[rel] = sha(raw)
    return json.loads(raw)
def canon(word):
    names = {}
    return tuple(names.setdefault(int(x), len(names)) for x in word)
def shape(word):
    return min(canon(word), canon(word[::-1]))
ap = argparse.ArgumentParser()
ap.add_argument('--outer', type=int, default=24)
ap.add_argument('--middle', type=int, default=24)
ap.add_argument('--rules', default='../120-nine-transition-window/data/full-rules.json')
ap.add_argument('--label')
args = ap.parse_args()
assert args.outer >= 0 and args.middle >= 0 and 4 * args.outer + args.middle <= 120
coefficients = [args.outer, args.outer, args.middle, args.outer, args.outer]
label = args.label or 'six-sum-guarded-graph'
folder = HERE / 'data' / label
folder.mkdir(exist_ok=True)
assert not (folder / 'results.json').exists(), 'Preserve previous experiment'
rules = read((HERE / args.rules).relative_to(ROOT).as_posix())
for rule in rules:
    assert len(set(rule['positions'])) == len(rule['positions'])
    assert rule['positions'] == sorted(4 - i for i in rule['positions']), 'Only reversal-symmetric sums in this experiment'
    probe = read(rule['probe'])
    assert probe['status'] == 'UNSAT_UNCERTIFIED'
    assert shape(probe['directions']) == shape(rule['directions'])
    assert probe['bounds'] == rule['bounds']
    assert canon(rule['directions']) == shape(rule['directions']), 'Bounds are in canonical orientation'
    assert canon(probe['directions']) == shape(probe['directions']), 'Probe bounds are in canonical orientation'
    assert probe.get('cap', probe.get('outer_sum_cap')) == rule['lower'] - 1
    assert probe.get('positions', [0,1,3,4]) == rule['positions']
prior_rules=read('milestones/117-cycle-sum-refinement/data/middle5-rules.json')
assert rules[:len(prior_rules)] == prior_rules
prior_result=read('milestones/117-cycle-sum-refinement/data/middle5-outer16/results.json')
prior_profiles={x['profile']:x for x in prior_result['profiles']}
previous119=read('milestones/119-shared-five-count-pressure/data/full-critical23/results.json')
previous119_profiles={x['profile']:x for x in previous119['profiles']}
previous120=read('milestones/120-nine-transition-window/data/outer3/results.json')
previous120_profiles={x['profile']:x for x in previous120['profiles']}
assert rules==previous119['rules']
start = time.monotonic()
graph = 'milestones/72-four-count-proof-closure/critical-current/'
meta = read(graph + 'data/source-proved-model.json')
gp = ROOT / (graph + 'build/source-graph.npz')
pins[gp.relative_to(ROOT).as_posix()] = sha(gp.read_bytes())
with np.load(gp) as z:
    arrays = {k: z[k] for k in z.files}
assert {k: sha(v.tobytes()) for k,v in arrays.items()} == meta['arrays_sha256']
ds = read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
completed = read('milestones/73-countfree-share-catalogue/data/proved-model.json')
conditional = read('milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json')
prior = read('milestones/111-critical-count-intervals/data/middle325-profiles/removed-indices.json')
previous_family = read('milestones/113-all-four-sum-pressure/data/pair24/removed-indices.json')
drop = np.zeros(len(arrays['U']), dtype=bool)
drop[prior] = True
code = arrays['count_code']
bonus = np.zeros(len(code), dtype=np.int64)
digits = np.stack([code // 6**j % 6 + 1 for j in range(5,-1,-1)], axis=1)
effects = []
for rule in rules:
    rejected = np.zeros(len(drop), dtype=bool)
    awarded = np.zeros(len(drop), dtype=bool)
    coefficient = min(coefficients[j] for j in rule['positions'])
    target = shape(rule['directions'])
    for di, word in enumerate(ds):
        lo, hi = np.searchsorted(arrays['direction'], [di, di+1])
        values = digits[lo:hi]
        for s in range(2):
            if shape(word[s+2:s+8]) != target:
                continue
            five = values[:,s:s+5]
            if canon(word[s+2:s+8]) != target:
                assert canon(word[s+2:s+8][::-1]) == target
                five = five[:,::-1]
            lower = np.array([b[0] for b in rule['bounds']])
            upper = np.array([b[1] for b in rule['bounds']])
            applicable = np.all((five >= lower) & (np.where(five == 6,21,five) <= upper),axis=1)
            selected = five[:,rule['positions']]
            demand = np.maximum(0, rule['lower'] - selected.sum(axis=1))
            rejected[lo:hi] |= applicable & (demand > 0) & np.all(selected < 6, axis=1)
            if s == 1:
                credit = np.where(applicable, coefficient*demand, 0)
                bonus[lo:hi] = np.maximum(bonus[lo:hi], credit)
                awarded[lo:hi] |= credit > 0
    effects.append(dict(name=rule['name'], coefficient=coefficient, rejected_keys=int(rejected.sum()),
        marginal_removed=int(np.count_nonzero(rejected & ~drop)), positive_credit_keys=int(awarded.sum())))
    drop |= rejected
    if rule['name'] == prior_rules[-1]['name']:
        previous_keep=~drop.copy();previous_bonus=bonus.copy()
        previous_removed=read('milestones/117-cycle-sum-refinement/data/middle5-outer16/removed-indices.json')
        assert np.array_equal(np.flatnonzero(drop),np.array(previous_removed))
before_guard=~drop.copy()
previous119_removed=read('milestones/119-shared-five-count-pressure/data/full-critical23/removed-indices.json')
assert np.array_equal(np.flatnonzero(drop),np.array(previous119_removed))
guard=read('milestones/120-nine-transition-window/data/probes/012031-outer3-radius3.json')
assert guard['status']=='UNSAT_UNCERTIFIED' and guard['directions']==[0,1,2,0,3,1]
assert guard['bounds']==[[0,3],[0,3],[0,21],[0,3],[0,3]] and guard['sum_cap'] is None
rejected=np.zeros(len(drop),dtype=bool)
for di,word in enumerate(ds):
    lo,hi=np.searchsorted(arrays['direction'],[di,di+1])
    for s in range(2):
        if shape(word[s+2:s+8])==tuple(guard['directions']):
            rejected[lo:hi]|=np.all(digits[lo:hi][:,[s,s+1,s+3,s+4]]<=3,axis=1)
guard_effect=dict(rejected_keys=int(rejected.sum()),newly_removed=int(np.count_nonzero(rejected & ~drop)))
drop|=rejected
previous120_removed=read('milestones/120-nine-transition-window/data/outer3/removed-indices.json')
assert np.array_equal(np.flatnonzero(drop),np.array(previous120_removed))
before_pair=~drop.copy()
pair_guards=read('milestones/121-replacement-window-pressure/data/pair-guards.json')
pair_effects=[]
pair_union=np.zeros(len(drop),dtype=bool)
for spec in pair_guards:
    pair_probe=read(spec['probe'])
    assert pair_probe['status']=='UNSAT_UNCERTIFIED' and pair_probe['directions']==[0,1,2,0,3,2]
    assert pair_probe['bounds']==spec['bounds'] and pair_probe['sum_cap'] is None and not pair_probe['sum_counter_added']
    lower=np.array([b[0] for b in spec['bounds']]);upper=np.array([b[1] for b in spec['bounds']])
    rejected=np.zeros(len(drop),dtype=bool)
    orientation_counts=[]
    for s in range(2):
        for reverse in [False,True]:
            oriented=np.zeros(len(drop),dtype=bool)
            for di,word in enumerate(ds):
                selected_word=word[s+2:s+8]
                if reverse:selected_word=selected_word[::-1]
                if canon(selected_word)!=(0,1,2,0,3,2):continue
                lo,hi=np.searchsorted(arrays['direction'],[di,di+1])
                five=digits[lo:hi,s:s+5]
                if reverse:five=five[:,::-1]
                oriented[lo:hi]=np.all((five>=lower)&(np.where(five==6,21,five)<=upper),axis=1)
            orientation_counts.append(dict(placement=s,reverse=reverse,hits=int(oriented.sum()),new_to120=int(np.count_nonzero(oriented&before_pair))))
            rejected|=oriented
    pair_effects.append(dict(name=spec['name'],bounds=spec['bounds'],rejected_keys=int(rejected.sum()),new_to120=int(np.count_nonzero(rejected&before_pair)),marginal_removed=int(np.count_nonzero(rejected&~drop)),orientation_counts=orientation_counts))
    pair_union|=rejected
    drop|=rejected
# Verify the expected clipped-count characterization independently of interval matching.
combined=np.zeros(len(drop),dtype=bool)
for di,word in enumerate(ds):
    lo,hi=np.searchsorted(arrays['direction'],[di,di+1])
    for s in range(2):
        if shape(word[s+2:s+8])!=(0,1,2,0,3,2):continue
        a,b=digits[lo:hi,s+1],digits[lo:hi,s+3]
        combined[lo:hi]|=(a<2)|(b<2)|(a+b<8)
assert np.array_equal(pair_union,combined)
old_cycle_survival=[]
for profile in previous120['profiles']:
    killed=[e['edge'] for e in profile['cycle'] if pair_union[e['edge']]]
    old_cycle_survival.append(dict(profile=profile['profile'],cycle_length=len(profile['cycle']),newly_removed_cycle_edges=killed))
removed = np.flatnonzero(drop)
assert np.all(drop[previous_family])
(folder / 'removed-indices.json').write_text(json.dumps(removed.tolist()) + '\n', encoding='utf-8')
keep = ~drop
original = np.flatnonzero(keep)
U, V, N = arrays['U'][keep], arrays['V'][keep], meta['states']
cf = {tuple(r['shape']): r['share'] for r in completed['countfree_floors']}
ff = cf | {(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
shapes = [shape(w[-6:]) for w in ds]

previous121=read('milestones/121-replacement-window-pressure/data/pair-graph/results.json')
previous121_profiles={p['profile']:p for p in previous121['profiles']}
previous121_removed=read('milestones/121-replacement-window-pressure/data/pair-graph/removed-indices.json')
assert np.array_equal(removed,np.array(previous121_removed))
assert previous121['edges']==len(U)
full_baselines={}
for name,old,floors in [('completed',completed,cf),('conditional_floor18',conditional,ff)]:
    floor=np.array([floors.get(s,0) for s in shapes],dtype=np.int64)
    baseline=np.maximum(arrays['weight'],120*(code.astype(np.int64)%6+1)+floor[arrays['direction']])
    assert sha(baseline.tobytes())==old['weight_sha256']
    full_baselines[name]=baseline+bonus
    assert sha(full_baselines[name][keep].tobytes())==previous121_profiles[name]['weight_sha256']
eligible=np.array([s==(0,1,2,0,3,2) for s in shapes])[arrays['direction']]
a,b=digits[:,2],digits[:,4]
eligible &= ((a==3)&(b==5))|((a==4)&(b==4))|((a==5)&(b==3))
assert not np.any(eligible & ((a==6)|(b==6)))
# Inspect exact suffix directions and pair values independently on every eligible key.
for di,word in enumerate(ds):
    lo,hi=np.searchsorted(arrays['direction'],[di,di+1])
    if not np.any(eligible[lo:hi]):continue
    assert canon(word[-6:])==(0,1,2,0,3,2) or canon(word[-6:][::-1])==(0,1,2,0,3,2)
    assert all(tuple(pair) in [(3,5),(4,4),(5,3)] for pair in np.unique(digits[lo:hi][eligible[lo:hi]][:,[2,4]],axis=0))
old_eligible={p['profile']:sum(bool(eligible[e['edge']]) for e in p['cycle']) for p in previous121['profiles']}
assert old_eligible['completed']==0 and old_eligible['conditional_floor18']==2



old_bonus24=bonus.copy();base_weights={name:full_baselines[name]-old_bonus24 for name in full_baselines}
case=read('milestones/32-seven-count-four-screen/data/cases.json')[10]
assert case['dirs']==[0,1,2,3,0,4,2] and case['bounds']==[[4,4]]*6
matching=np.array([canon(word[2:])==tuple(case['dirs']) or canon(word[2:][::-1])==tuple(case['dirs']) for word in ds])[arrays['direction']]
guarded=matching & (digits[:,0]<6)
six_sum=digits.sum(axis=1);all_exact=np.all(digits<6,axis=1)
probe25=read('milestones/123-six-count-recovery/data/probes/0123042-total24-full.json');assert probe25['status']=='UNSAT_UNCERTIFIED' and probe25['cap']==24
probe26=read('milestones/123-six-count-recovery/data/probes/0123042-total25-resume.json');assert probe26['status']=='UNSAT_UNCERTIFIED' and probe26['cap']==25
prior20=read('milestones/123-six-count-recovery/data/six-sum-graph-l25/results.json')
conditional_cycle=next(p for p in prior20['profiles'] if p['profile']=='conditional_floor18')['cycle']
summary=dict(status='RUNNING_GUARDED24_FLOOR_TEST',requested_floors=[25,26],completed=[],skipped=[],coefficient=24,guard='First of six clipped symbols is below6; its actual count is exact.',shared_budget='MAX of old24bonus and guarded24six-deficit, using only lastfive excess counts.',source_files_sha256=pins,script_sha256=sha(Path(__file__).read_bytes()),scope='Conditional graph experiment. Floors25and26have native negative evidence only; concrete refutations, guarded last-five accounting and actual global assembly require separate proof. No global bound.')
sp=folder/'summary.json';assert not sp.exists()
def save():sp.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
save()
for L in [25,26]:
    outdir=HERE/'data'/('six-sum-guarded-graph-l'+str(L));assert not outdir.exists();outdir.mkdir()
    new_bonus=24*np.where(guarded,np.maximum(0,L-six_sum),0)
    shared=np.maximum(old_bonus24,new_bonus)
    rejected=matching & all_exact & (six_sum<L)
    assert np.all(~rejected|guarded)
    mask=keep & ~rejected
    ids=np.flatnonzero(mask);u=arrays['U'][mask];v=arrays['V'][mask]
    (outdir/'removed-indices.json').write_text(json.dumps(np.flatnonzero(~mask).tolist())+'\n',encoding='utf-8')
    rows=[]
    for name in ['completed','conditional_floor18']:
        old=previous121_profiles[name];cycle=old['cycle'] if name=='completed' else conditional_cycle
        assert all(not matching[e['edge']] and not guarded[e['edge']] and not eligible[e['edge']] for e in cycle)
        W=(base_weights[name]+shared)[mask]
        ci=np.searchsorted(ids,np.array([e['edge'] for e in cycle]));assert np.array_equal(ids[ci],np.array([e['edge'] for e in cycle]))
        mean=Fraction(int(W[ci].sum()),len(ci));assert str(mean)==old['mean'];p,d=mean.numerator,mean.denominator
        potpath=ROOT/'milestones/121-replacement-window-pressure/data/pair-graph'/old['potential_file'];pins[potpath.relative_to(ROOT).as_posix()]=sha(potpath.read_bytes())
        packed=potpath.read_bytes();raw=gzip.decompress(packed);assert sha(raw)==old['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8');assert len(pi)==N and pi.min()==0 and pi.max()==old['range_scaled']
        assert np.all(p+pi[v]<=d*W+pi[u])
        assert all(p+int(pi[v[e]])==d*W[e]+int(pi[u[e]]) for e in ci)
        R=int(pi.max());bound=Fraction(1098960*d+8*p+R,4200*d+p)
        (outdir/old['potential_file']).write_bytes(packed)
        fullcycle=[]
        for e in ci:
            k=int(ids[e]);fullcycle.append(dict(edge=k,directions=ds[int(arrays['direction'][k])],counts=digits[k].tolist(),history=int(arrays['history'][k]),u=int(u[e]),v=int(v[e]),weight=int(W[e]),base_weight=int(base_weights[name][k]),old_bonus24=int(old_bonus24[k]),guarded_six_bonus24=int(new_bonus[k]),shared_bonus=int(shared[k]),six_matching=bool(matching[k]),guarded=bool(guarded[k]),endpoint_eligible=bool(eligible[k])))
        row=dict(profile=name,L=L,mean=str(mean),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=fullcycle,cycle_six_matching=0,cycle_guarded_matching=0,cycle_endpoint_eligible=0,weight_sha256=sha(W.tobytes()),potential_file=old['potential_file'],potential_sha256=sha(raw),potential_reused_from121_and_rechecked_on_all_edges=True,all_edge_inequalities_checked=True,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator)
        rows.append(row);print('guarded24',L,name,'mean',mean,'range',row['range'],'bound',bound,'integer',row['comparison_integer_bound'],flush=True)
    out=dict(status='EXACT_GUARDED24_FINITE_PROFILES',L=L,profiles=rows,states=N,edges=len(ids),newly_removed=int(np.count_nonzero(rejected&keep)),new_guarded_credit_keys=int(np.count_nonzero((new_bonus>old_bonus24)&mask)),shared_bonus_is_maximum=True,source_files_sha256=pins,algorithm_sha256=algsha,script_sha256=sha(Path(__file__).read_bytes()),scope=summary['scope'])
    rp=outdir/'results.json';rp.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');summary['completed'].append(dict(L=L,results=rp.relative_to(HERE).as_posix(),results_sha256=sha(rp.read_bytes()),profiles=[{k:p[k] for k in ['profile','mean','range','comparison_bound','comparison_integer_bound','cycle_guarded_matching']} for p in rows]));save()
    if all(p['cycle_guarded_matching']==0 for p in rows):
        summary['skipped']=[x for x in [25,26] if x>L];summary['skip_reason']='Both attaining cycles avoid all matching six-count windows and endpoint events. Monotonicity and these fixed cycles establish unchanged means for every larger floor; zero-range comparisons already prohibit integer improvement.';break
assert all(sha((ROOT/p).read_bytes())==d for p,d in pins.items())
summary['status']='PASS_GUARDED24_AND_UNBOUNDED_FLOOR_OBSTRUCTION';summary['seconds']=time.monotonic()-start;save()
print('Guarded24experiment complete',flush=True)
