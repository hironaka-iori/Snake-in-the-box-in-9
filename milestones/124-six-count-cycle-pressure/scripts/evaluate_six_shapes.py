"""Combined conditional six-count floors with guarded last-five credit."""
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
label = args.label or 'graph-26-25-25'
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
(folder / 'baseline121-removed-indices.json').write_text(json.dumps(removed.tolist()) + '\n', encoding='utf-8')
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



old_bonus24=bonus.copy()
base_weights={name:full_baselines[name]-old_bonus24 for name in full_baselines}
cases=read('milestones/124-six-count-cycle-pressure/data/cases.json')
assert [shape(c['directions']) for c in cases]==[(0,1,2,0,3,1,0),(0,1,2,3,0,2,4)]
assert all(c['cap']==24 and c['bounds']==[[0,21]]*6 and c['positions']==list(range(6)) for c in cases)
prior_probe=read('milestones/123-six-count-recovery/data/probes/0123042-total25-resume.json')
assert prior_probe['status']=='UNSAT_UNCERTIFIED' and prior_probe['cap']==25 and prior_probe['directions']==[0,1,2,3,0,4,2]
specs=[dict(shape=[0,1,2,3,0,4,2],floor=26),dict(shape=[0,1,2,0,3,1,0],floor=25),dict(shape=[0,1,2,3,0,2,4],floor=25)]
six_shapes=[shape(word[2:]) for word in ds]
six_sum=digits.sum(axis=1);all_exact=np.all(digits<6,axis=1)
new_bonus=np.zeros(len(code),dtype=np.int64)
rejected=np.zeros(len(code),dtype=bool)
matching=np.zeros(len(code),dtype=bool)
six_effects=[]
for spec in specs:
    target=tuple(spec['shape']);L=spec['floor']
    match=np.array([s==target for s in six_shapes])[arrays['direction']]
    guard=match & (digits[:,0]<6)
    extra=24*np.where(guard,np.maximum(0,L-six_sum),0)
    reject=match & all_exact & (six_sum<L)
    assert np.all(~reject|guard)
    six_effects.append(dict(shape=spec['shape'],floor=L,matched121_keys=int(np.count_nonzero(match&keep)),guarded121_keys=int(np.count_nonzero(guard&keep)),newly_removed=int(np.count_nonzero(reject&keep)),increased_credit_before_other_removals=int(np.count_nonzero((extra>old_bonus24)&keep&~reject))))
    new_bonus=np.maximum(new_bonus,extra);rejected|=reject;matching|=match
shared=np.maximum(old_bonus24,new_bonus)
mask=keep&~rejected
ids=np.flatnonzero(mask);u=arrays['U'][mask];v=arrays['V'][mask]
(folder/'removed-indices.json').write_text(json.dumps(np.flatnonzero(~mask).tolist())+'\n',encoding='utf-8')
rows=[]
for name in ['completed','conditional_floor18']:
    old=previous121_profiles[name];cycle=old['cycle']
    W=(base_weights[name]+shared)[mask]
    edge_ids=np.array([e['edge'] for e in cycle])
    ci=np.searchsorted(ids,edge_ids)
    assert np.array_equal(ids[ci],edge_ids), 'An old attaining cycle is removed; stop for requested follow-up.'
    assert all(v[ci[j]]==u[ci[(j+1)%len(ci)]] for j in range(len(ci)))
    assert not np.any(matching[edge_ids]), 'Cycle matches a target; inspect before stronger experiments.'
    mean=Fraction(int(W[ci].sum()),len(ci));assert str(mean)==old['mean']
    p,d=mean.numerator,mean.denominator
    potpath=ROOT/'milestones/121-replacement-window-pressure/data/pair-graph'/old['potential_file']
    packed=potpath.read_bytes();pins[potpath.relative_to(ROOT).as_posix()]=sha(packed)
    raw=gzip.decompress(packed);assert sha(raw)==old['potential_sha256']
    pi=np.frombuffer(raw,dtype='<i8');assert len(pi)==N and pi.min()==0 and pi.max()==old['range_scaled']
    slack=d*W+pi[u]-p-pi[v]
    assert np.all(slack>=0)
    assert np.all(slack[ci]==0)
    R=int(pi.max());bound=Fraction(1098960*d+8*p+R,4200*d+p);zero_range=Fraction(1098960*d+8*p,4200*d+p)
    (folder/old['potential_file']).write_bytes(packed)
    fullcycle=[]
    for e in ci:
        k=int(ids[e]);word=ds[int(arrays['direction'][k])];suffix=word[2:]
        fullcycle.append(dict(edge=k,directions=word,suffix_directions=suffix,suffix_forward=list(canon(suffix)),suffix_reverse=list(canon(suffix[::-1])),suffix_shape=list(shape(suffix)),counts=digits[k].tolist(),six_sum=int(six_sum[k]),first_symbol_exact=bool(digits[k,0]<6),u=int(u[e]),v=int(v[e]),weight=int(W[e]),base_weight=int(base_weights[name][k]),old_bonus24=int(old_bonus24[k]),new_guarded_bonus24=int(new_bonus[k]),shared_bonus=int(shared[k]),matches_any_shape=bool(matching[k]),endpoint_eligible=bool(eligible[k]),first_floor_changing_weight_or_retention=None))
    row=dict(profile=name,mean=str(mean),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=fullcycle,cycle_matching_keys=int(np.count_nonzero(matching[edge_ids])),cycle_endpoint_eligible=int(np.count_nonzero(eligible[edge_ids])),weight_sha256=sha(W.tobytes()),potential_file=old['potential_file'],potential_sha256=sha(raw),potential_reused_from121=True,all_edge_inequalities_checked=True,inequalities_checked=len(W),minimum_slack=int(slack.min()),cycle_attaining=True,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,zero_range_comparison=str(zero_range),all_larger_target_floors_same_mean=True)
    rows.append(row);print(name,'mean',mean,'range',row['range'],'bound',bound,'integer',row['comparison_integer_bound'],'target matches',row['cycle_matching_keys'],'endpoint events',row['cycle_endpoint_eligible'],flush=True)
assert all(sha((ROOT/path).read_bytes())==digest for path,digest in pins.items())
out=dict(status='PASS_CONDITIONAL_THREE_SHAPE_GRAPH_AND_ALL_FLOOR_OBSTRUCTION',specs=specs,profiles=rows,states=N,edges=len(ids),baseline121_edges=int(keep.sum()),newly_removed=int(np.count_nonzero(rejected&keep)),new_guarded_credit_keys=int(np.count_nonzero((new_bonus>old_bonus24)&mask)),effects=six_effects,shared_bonus_is_maximum=True,old24_bonus_preserved=True,guard='First chronological clipped symbol below6. Reversal affects only shape recognition, never count order or guard position.',six_symbol_interval=[6,21],deletion_requires_all_six_exact=True,baseline121_weight_hashes_reproduced=True,source_files_sha256=pins,algorithm_sha256=algsha,script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,scope='Conditional finite graph experiment. The three new local floors and inherited count-sum hypotheses remain unproved. Checked generic guarded accounting does not supply the local premises or full graph-to-snake assembly. No actual-snake upper bound.')
(folder/'results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Combined guarded24 experiment complete',flush=True)
