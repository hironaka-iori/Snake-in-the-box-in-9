"""Conditional graph experiments with one shared weighted excess budget."""
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
ap.add_argument('--rules', default='data/total-rules.json')
ap.add_argument('--label')
args = ap.parse_args()
assert args.outer >= 0 and args.middle >= 0 and 4 * args.outer + args.middle <= 120
coefficients = [args.outer, args.outer, args.middle, args.outer, args.outer]
label = args.label or f'outer{args.outer}-middle{args.middle}'
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
removed = np.flatnonzero(drop)
assert np.all(drop[previous_family])
(folder / 'removed-indices.json').write_text(json.dumps(removed.tolist()) + '\n', encoding='utf-8')
keep = ~drop
original = np.flatnonzero(keep)
U, V, N = arrays['U'][keep], arrays['V'][keep], meta['states']
cf = {tuple(r['shape']): r['share'] for r in completed['countfree_floors']}
ff = cf | {(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
shapes = [shape(w[-6:]) for w in ds]
pool = np.flatnonzero(alg['prune'](N,U,V))
active = np.unique(np.concatenate([U[pool],V[pool]]))
index = np.full(N,-1,dtype=np.int32)
index[active] = np.arange(len(active))
profiles = []
for name,old,floors in [('completed',completed,cf),('conditional_floor18',conditional,ff)]:
    before = time.monotonic()
    floor = np.array([floors.get(s,0) for s in shapes],dtype=np.int64)
    baseline = np.maximum(arrays['weight'],120*(code.astype(np.int64)%6+1)+floor[arrays['direction']])
    assert sha(baseline.tobytes()) == old['weight_sha256']
    assert sha((baseline+previous_bonus)[previous_keep].tobytes()) == prior_profiles[name]['weight_sha256'], 'Previous full weight vector changed'
    W = (baseline+bonus)[keep]
    _,cy = alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400)
    ci = pool[np.asarray(cy)]
    mu = Fraction(int(W[ci].sum()),len(ci))
    p,d = mu.numerator,mu.denominator
    assert all(V[ci[i]] == U[ci[(i+1)%len(ci)]] for i in range(len(ci)))
    dist = np.zeros(N,dtype=np.int64)
    for iteration in range(1,1501):
        nxt = dist.copy()
        np.minimum.at(nxt,V,dist[U]+d*W-p)
        if np.array_equal(nxt,dist):
            break
        dist = nxt
    else:
        raise AssertionError('Potential did not converge')
    assert np.all(p+dist[V] <= d*W+dist[U])
    pi = dist-dist.min()
    R = int(pi.max())
    buf = pi.astype('<i8').tobytes()
    filename = name+'-potential.i64.gz'
    (folder/filename).write_bytes(gzip.compress(buf,mtime=0))
    bound = Fraction(1098960*d+8*p+R,4200*d+p)
    cycle = [dict(edge=int(original[e]),direction=int(arrays['direction'][original[e]]),history=int(arrays['history'][original[e]]),
        count_code=int(arrays['count_code'][original[e]]),u=int(U[e]),v=int(V[e]),weight=int(W[e]),bonus=int(bonus[original[e]])) for e in ci]
    profiles.append(dict(profile=name,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,
        weight_sha256=sha(W.tobytes()),potential_file=filename,potential_sha256=sha(buf),all_edge_inequalities_checked=True,
        iterations=iteration,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,seconds=time.monotonic()-before))
    print(label,name,'mean',mu,'range',Fraction(R,d),'comparison',bound,'integer',bound.numerator//bound.denominator,flush=True)
assert all(sha((ROOT/p).read_bytes()) == digest for p,digest in pins.items())
out = dict(status='EXACT_FINITE_PROFILES_WITH_UNPROVED_SUM_RULES',rules=rules,coefficients=coefficients,effects=effects,
    profiles=profiles,states=N,edges=len(U),additional_removed=len(removed)-len(prior),additional_to_previous_family=len(removed)-len(previous_family),
    prior117_full_weights_and_removals_reproduced=True,additional_to117=len(removed)-len(previous_removed),bonus_edges=int(np.count_nonzero(bonus[keep])),source_files_sha256=pins,algorithm_sha256=algsha,script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
    scope='Conditional native graph experiment only. The new total-count inequality and remaining sum hypotheses require checked proofs. Credit is the maximum applicable suffix deficit with one shared coefficient budget, not a sum of competing bonuses. Complete Lean graph and actual-snake integration remain pending; no new global bound.')
(folder/'results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Additional removed',out['additional_removed'],'beyond previous family',out['additional_to_previous_family'],flush=True)
