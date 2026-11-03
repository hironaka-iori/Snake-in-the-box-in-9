"""Bounded six-count case10 deletion and endpoint-credit experiments."""
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
label = args.label or 'six-graph'
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

def graph_data(mask):
    ids=np.flatnonzero(mask);u=arrays['U'][mask];v=arrays['V'][mask]
    pool=np.flatnonzero(alg['prune'](N,u,v));active=np.unique(np.concatenate([u[pool],v[pool]]));index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active))
    return ids,u,v,pool,active,index

def calculate(name,C,budget,mask,graph,outdir,fixed_cycle=None):
    before=time.monotonic();ids,u,v,pool,active,index=graph
    W=full_baselines[name][mask]+C*eligible[mask].astype(np.int64)
    if fixed_cycle is None:
        _,cy=alg['howard'](len(active),index[u[pool]],index[v[pool]],W[pool],iters=400);ci=pool[np.asarray(cy)]
    else:
        edge_ids=np.array([e['edge'] for e in fixed_cycle]);ci=np.searchsorted(ids,edge_ids);assert np.array_equal(ids[ci],edge_ids)
    mu=Fraction(int(W[ci].sum()),len(ci));p,d=mu.numerator,mu.denominator
    assert all(v[ci[i]]==u[ci[(i+1)%len(ci)]] for i in range(len(ci)))
    dist=np.zeros(N,dtype=np.int64)
    for iteration in range(1,1501):
        nxt=dist.copy();np.minimum.at(nxt,v,dist[u]+d*W-p)
        if np.array_equal(nxt,dist):break
        dist=nxt
    else:raise AssertionError('Potential did not converge')
    assert np.all(p+dist[v]<=d*W+dist[u])
    pi=dist-dist.min();R=int(pi.max());buf=pi.astype('<i8').tobytes();filename=name+'-potential.i64.gz'
    (outdir/filename).write_bytes(gzip.compress(buf,mtime=0))
    bound=Fraction(1098960*d+budget*C*d+8*p+R,4200*d+p)
    cycle=[dict(edge=int(ids[e]),direction=int(arrays['direction'][ids[e]]),history=int(arrays['history'][ids[e]]),count_code=int(arrays['count_code'][ids[e]]),directions=ds[int(arrays['direction'][ids[e]])],counts=digits[ids[e]].tolist(),u=int(u[e]),v=int(v[e]),weight=int(W[e]),base_weight=int(full_baselines[name][ids[e]]),eligible=bool(eligible[ids[e]]),credit=int(C*eligible[ids[e]]),bonus=int(bonus[ids[e]])) for e in ci]
    row=dict(profile=name,C=C,occurrence_budget=budget,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,cycle_eligible=sum(e['eligible'] for e in cycle),weight_sha256=sha(W.tobytes()),potential_file=filename,potential_sha256=sha(buf),all_edge_inequalities_checked=True,edges=len(u),iterations=iteration,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,seconds=time.monotonic()-before)
    print(outdir.name,name,'mean',mu,'range',Fraction(R,d),'corrected',bound,'integer',row['comparison_integer_bound'],'cycle eligible',row['cycle_eligible'],flush=True)
    return row


cases32=read('milestones/32-seven-count-four-screen/data/cases.json')
meta10=read('milestones/32-seven-count-four-screen/data/four10.json')
case=cases32[10]
assert case['dirs']==meta10['dirs']==[0,1,2,3,0,4,2]
assert case['bounds']==meta10['bounds']==[[4,4]]*6
assert canon(case['dirs'][::-1])==tuple(case['dirs'])
all_four=np.all(digits==4,axis=1)
assert np.array_equal(all_four,code==27993)
direction10=np.array([canon(word[2:])==tuple(case['dirs']) or canon(word[2:][::-1])==tuple(case['dirs']) for word in ds])
case10=all_four & direction10[arrays['direction']]
assert case10[3049577] and not case10[1275804] and not case10[988624]
case_keep=keep & ~case10
case_removed=np.flatnonzero(~case_keep)
(folder/'case10-removed-indices.json').write_text(json.dumps(case_removed.tolist())+'\n',encoding='utf-8')
prior122=read('milestones/122-endpoint-equality/data/endpoint-graph-c4/results.json')
prior122_cycles=[dict(profile=p['profile'],cycle_length=len(p['cycle']),newly_removed_cycle_edges=[e['edge'] for e in p['cycle'] if case10[e['edge']]]) for p in prior122['profiles']]
summary=dict(status='RUNNING_CONDITIONAL_SIX_COUNT_EXPERIMENT',case_index=10,case=case,case10_source_keys=int(case10.sum()),case10_newly_removed=int(np.count_nonzero(case10&keep)),all_four_retained_keys=int(np.count_nonzero(all_four&keep)),endpoint_eligible_remaining=int(np.count_nonzero(eligible&case_keep)),prior122_cycles=prior122_cycles,occurrence_budget=13,credit_schedule=[4,16,32,64],completed_credit_cases=[],skipped_credit_cases=[],case10_alone=None,ideal_endpoint_deletion=None,all_four_diagnostic=None,source_files_sha256=pins,script_sha256=sha(Path(__file__).read_bytes()),scope='Conditional finite graph experiments only. Case10 exclusion, the endpoint occurrence budget13 and inherited sum rules require their separate completed proofs. Ideal endpoint deletion is a stronger hypothetical restriction; all-four diagnostic additionally assumes all34six-count exclusions. No global bound.')
summary_path=folder/'summary.json';assert not summary_path.exists()
def save_summary():summary_path.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
save_summary()

def experiment(label,mask,C,budget,fixed_conditional=None,description=''):
    outdir=HERE/'data'/label;assert not outdir.exists();outdir.mkdir()
    graph=graph_data(mask)
    rows=[]
    for name in ['completed','conditional_floor18']:
        fixed=previous121_profiles[name]['cycle'] if name=='completed' else fixed_conditional
        rows.append(calculate(name,C,budget,mask,graph,outdir,fixed))
    (outdir/'removed-indices.json').write_text(json.dumps(np.flatnonzero(~mask).tolist())+'\n',encoding='utf-8')
    out=dict(status='EXACT_FINITE_PROFILES_WITH_UNPROVED_SIX_COUNT_AND_ENDPOINT_PREMISES',label=label,C=C,occurrence_budget=budget,profiles=rows,states=N,edges=int(mask.sum()),source_files_sha256=pins,algorithm_sha256=algsha,script_sha256=sha(Path(__file__).read_bytes()),scope=description+' '+summary['scope'])
    rp=outdir/'results.json';rp.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    return dict(results=rp.relative_to(HERE).as_posix(),results_sha256=sha(rp.read_bytes()),profiles=[{k:p[k] for k in ['profile','mean','range','comparison_bound','comparison_integer_bound','cycle_eligible']} for p in rows]),rows

base,base_rows=experiment('six-graph-case10',case_keep,0,0,previous121_profiles['conditional_floor18']['cycle'],'Case10 deletion alone.')
summary['case10_alone']=base;save_summary()
ideal_mask=case_keep & ~eligible
ideal,ideal_rows=experiment('six-graph-ideal',ideal_mask,0,0,None,'Case10 plus deletion of every endpoint-eligible suffix; ideal zero-budget experiment.')
summary['ideal_endpoint_deletion']=ideal;save_summary()
saturated=None
for C in summary['credit_schedule']:
    fixed=ideal_rows[1]['cycle'] if ideal_rows[1]['mean']==base_rows[1]['mean'] else None
    entry,rows=experiment('six-graph-c'+str(C),case_keep,C,13,fixed,'Case10 plus endpoint credit with occurrence bound13.')
    entry['C']=C;summary['completed_credit_cases'].append(entry);save_summary()
    if rows[1]['cycle_eligible']==0:
        saturated=rows[1];summary['skipped_credit_cases']=[c for c in summary['credit_schedule'] if c>C]
        summary['saturation_reason']='An attaining conditional cycle has no eligible suffix and fixes an upper ceiling on the minimum mean for larger coefficients.';save_summary();break
if ideal_rows[1]['mean']==base_rows[1]['mean']:
    diagnostic_mask=keep & ~all_four & ~eligible
    diagnostic,diagnostic_rows=experiment('six-graph-all4-ideal',diagnostic_mask,0,0,None,'Stronger34-case diagnostic: delete every six-count-all4key and every eligible endpoint suffix.')
    summary['all_four_diagnostic']=diagnostic;save_summary()
assert all(sha((ROOT/p).read_bytes())==d for p,d in pins.items())
summary['status']='PASS_BOUNDED_CONDITIONAL_SIX_COUNT_EXPERIMENT';summary['seconds']=time.monotonic()-start;save_summary()
print('Completed bounded case10 experiment',flush=True)
