"""Four conditional six-count sum-floor sensitivities with a shared20-per-centre budget."""
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
label = args.label or 'six-sum-graph'
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


assert np.all(bonus%24==0)
old_bonus24=bonus.copy();old_bonus20=20*(old_bonus24//24)
base_weights={name:full_baselines[name]-old_bonus24 for name in full_baselines}
case=read('milestones/32-seven-count-four-screen/data/cases.json')[10]
assert case['dirs']==[0,1,2,3,0,4,2] and case['bounds']==[[4,4]]*6
assert canon(case['dirs'][::-1])==tuple(case['dirs'])
matching=np.array([canon(word[2:])==tuple(case['dirs']) or canon(word[2:][::-1])==tuple(case['dirs']) for word in ds])[arrays['direction']]
six_sum=digits.sum(axis=1);all_exact=np.all(digits<6,axis=1)
probe=read('milestones/123-six-count-recovery/data/probes/0123042-total24-full.json')
assert probe['status']=='UNSAT_UNCERTIFIED' and probe['cap']==24 and probe['directions']==case['dirs'] and probe['bounds']==[[0,21]]*6
probe25=read('milestones/123-six-count-recovery/data/probes/0123042-total25-full.json')
assert probe25['cap']==25 and probe25['directions']==case['dirs']
summary=dict(status='RUNNING_CONDITIONAL_SIX_SUM_SENSITIVITY',floors=[25,26,27,28],old_coefficient=24,new_coefficients=[20]*6,old_bonus24_divisibility_checked=True,baseline121_weight_hashes_reproduced=True,native_floor25_probe_status=probe['status'],floor26_probe_status=probe25['status'],cases=[],optional_endpoint=None,source_files_sha256=pins,script_sha256=sha(Path(__file__).read_bytes()),scope='Conditional six-count floor sensitivity. L25 has an uncertified native negative probe; L26probe does not establish a floor; L27/28 are hypothetical. Every floor, all inherited sum rules,20/six-overlap accounting and full global assembly require separate proof. No global bound.')
summary_path=folder/'summary.json';assert not summary_path.exists()
def save_summary():summary_path.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
save_summary()

def graph_data(mask):
    ids=np.flatnonzero(mask);u=arrays['U'][mask];v=arrays['V'][mask]
    pool=np.flatnonzero(alg['prune'](N,u,v));active=np.unique(np.concatenate([u[pool],v[pool]]));index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active))
    return ids,u,v,pool,active,index

def evaluate(L,C=0,budget=0):
    label='six-sum-graph-l'+str(L)+('-c'+str(C) if C else '')
    outdir=HERE/'data'/label;assert not outdir.exists();outdir.mkdir()
    deficit=np.where(matching,np.maximum(0,L-six_sum),0)
    six_bonus20=20*deficit
    shared_bonus=np.maximum(old_bonus20,six_bonus20)
    rejected=matching & all_exact & (six_sum<L)
    mask=keep & ~rejected
    ids,u,v,pool,active,index=graph_data(mask)
    (outdir/'removed-indices.json').write_text(json.dumps(np.flatnonzero(~mask).tolist())+'\n',encoding='utf-8')
    rows=[]
    for name in ['completed','conditional_floor18']:
        before=time.monotonic();W=(base_weights[name]+shared_bonus+C*eligible.astype(np.int64))[mask]
        _,cy=alg['howard'](len(active),index[u[pool]],index[v[pool]],W[pool],iters=400);ci=pool[np.asarray(cy)]
        mu=Fraction(int(W[ci].sum()),len(ci));p,d=mu.numerator,mu.denominator
        assert all(v[ci[i]]==u[ci[(i+1)%len(ci)]] for i in range(len(ci)))
        dist=np.zeros(N,dtype=np.int64)
        for iteration in range(1,1501):
            nxt=dist.copy();np.minimum.at(nxt,v,dist[u]+d*W-p)
            if np.array_equal(nxt,dist):break
            dist=nxt
        else:raise AssertionError('Potential did not converge')
        assert np.all(p+dist[v]<=d*W+dist[u])
        pi=dist-dist.min();R=int(pi.max());buf=pi.astype('<i8').tobytes();filename=name+'-potential.i64.gz';(outdir/filename).write_bytes(gzip.compress(buf,mtime=0))
        bound=Fraction(1098960*d+budget*C*d+8*p+R,4200*d+p)
        cycle=[]
        for e in ci:
            k=int(ids[e]);change=None
            if matching[k]:change=int(six_sum[k])+1 if all_exact[k] else int(six_sum[k]+old_bonus20[k]//20+1)
            cycle.append(dict(edge=k,direction=int(arrays['direction'][k]),history=int(arrays['history'][k]),count_code=int(code[k]),directions=ds[int(arrays['direction'][k])],counts=digits[k].tolist(),u=int(u[e]),v=int(v[e]),weight=int(W[e]),base_weight=int(base_weights[name][k]),old_bonus24=int(old_bonus24[k]),old_bonus20=int(old_bonus20[k]),six_matching=bool(matching[k]),six_sum=int(six_sum[k]),six_deficit=int(deficit[k]),six_bonus20=int(six_bonus20[k]),shared_bonus=int(shared_bonus[k]),endpoint_eligible=bool(eligible[k]),endpoint_credit=int(C*eligible[k]),first_floor_changing_weight_or_retention=change))
        thresholds=[e['first_floor_changing_weight_or_retention'] for e in cycle if e['first_floor_changing_weight_or_retention'] is not None]
        row=dict(profile=name,L=L,C=C,occurrence_budget=budget,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,cycle_six_matching=sum(e['six_matching'] for e in cycle),cycle_endpoint_eligible=sum(e['endpoint_eligible'] for e in cycle),cycle_first_changing_floor=min(thresholds) if thresholds else None,weight_sha256=sha(W.tobytes()),potential_file=filename,potential_sha256=sha(buf),all_edge_inequalities_checked=True,iterations=iteration,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,seconds=time.monotonic()-before)
        rows.append(row);print(label,name,'mean',mu,'range',Fraction(R,d),'bound',bound,'integer',row['comparison_integer_bound'],'six matches',row['cycle_six_matching'],'endpoint matches',row['cycle_endpoint_eligible'],flush=True)
    out=dict(status='EXACT_FINITE_SIX_SUM_FLOOR_SENSITIVITY',L=L,C=C,occurrence_budget=budget,profiles=rows,states=N,edges=len(u),newly_removed=int(np.count_nonzero(rejected&keep)),new_six_credit_keys=int(np.count_nonzero((six_bonus20>old_bonus20)&mask)),old_bonus_scaled_to20=True,shared_bonus_is_maximum=True,source_files_sha256=pins,algorithm_sha256=algsha,script_sha256=sha(Path(__file__).read_bytes()),scope=summary['scope'])
    rp=outdir/'results.json';rp.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    return dict(L=L,C=C,results=rp.relative_to(HERE).as_posix(),results_sha256=sha(rp.read_bytes()),profiles=[{k:p[k] for k in ['profile','mean','range','comparison_bound','comparison_integer_bound','cycle_six_matching','cycle_endpoint_eligible','cycle_first_changing_floor']} for p in rows]),rows

all_rows=[]
for L in [25,26,27,28]:
    entry,rows=evaluate(L);summary['cases'].append(entry);all_rows.append((L,rows));save_summary()
bestL,bestRows=min(all_rows,key=lambda t:(Fraction(t[1][1]['comparison_bound']),t[0]))
summary['best_floor_for_conditional_profile']=bestL
if bestRows[1]['cycle_endpoint_eligible']>0:
    entry,rows=evaluate(bestL,4,13);summary['optional_endpoint']=entry
else:summary['optional_endpoint_skipped']='The attaining conditional cycle at the best floor has no eligible endpoint suffix, so endpoint credit cannot raise its mean.'
assert all(sha((ROOT/p).read_bytes())==d for p,d in pins.items())
summary['status']='PASS_BOUNDED_CONDITIONAL_SIX_SUM_SENSITIVITY';summary['seconds']=time.monotonic()-start;save_summary()
print('Completed four six-count floor sensitivities',flush=True)
