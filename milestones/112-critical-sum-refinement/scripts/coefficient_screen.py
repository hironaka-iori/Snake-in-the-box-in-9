"""Bound coefficient choices using already verified attaining cycles."""
from pathlib import Path
from fractions import Fraction
import hashlib, json
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
pins = {}
def read(p):
    raw = p.read_bytes()
    pins[p.relative_to(ROOT).as_posix()] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw)
def canon(word):
    labels = {}
    return tuple(labels.setdefault(x,len(labels)) for x in word)
def shape(word):
    return min(canon(word),canon(word[::-1]))
ds = read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
rules = read(HERE/'data/proposed-rules.json')
cycles = []
for label in ['outer24-middle24','outer30-middle0']:
    result = read(HERE/'data'/label/'results.json')
    for profile in result['profiles']:
        cycle = []
        for e in profile['cycle']:
            xs = [e['count_code']//6**j%6+1 for j in range(5,-1,-1)][1:]
            target = shape(ds[e['direction']][-6:])
            d4 = d5 = 0
            for rule in rules:
                if shape(rule['directions']) != target:
                    continue
                lo,hi = rule['middle_bounds']
                if not (lo <= xs[2] and (21 if xs[2] == 6 else xs[2]) <= hi):
                    continue
                demand = max(0,rule['lower']-sum(xs[j] for j in rule['positions']))
                if len(rule['positions']) == 4:
                    d4 = max(d4,demand)
                else:
                    assert len(rule['positions']) == 5
                    d5 = max(d5,demand)
            a,b = result['coefficients'][0],result['coefficients'][2]
            assert max(a*d4,min(a,b)*d5) == e['bonus']
            cycle.append(dict(edge=e['edge'],u=e['u'],v=e['v'],baseline=e['weight']-e['bonus'],outer_deficit=d4,total_deficit=d5))
        assert all(cycle[i]['v'] == cycle[(i+1)%len(cycle)]['u'] for i in range(len(cycle)))
        cycles.append(dict(source=label,profile=profile['profile'],cycle=cycle))
rows = []
for a in range(31):
    b = 120-4*a
    profile_bounds = {}
    for profile in ['completed','conditional_floor18']:
        means = [sum((Fraction(e['baseline']+max(a*e['outer_deficit'],min(a,b)*e['total_deficit'])) for e in c['cycle']),Fraction())/len(c['cycle'])
            for c in cycles if c['profile'] == profile]
        profile_bounds[profile] = str(min(means))
    rows.append(dict(outer=a,middle=b,upper_bounds=profile_bounds))
best = max(Fraction(r['upper_bounds']['completed']) for r in rows)
winners = [r['outer'] for r in rows if Fraction(r['upper_bounds']['completed']) == best]
out = dict(status='EXACT_CYCLE_UPPER_BOUNDS_FOR_INTEGER_COEFFICIENTS',cycles=cycles,rows=rows,
    best_completed_upper_bound=str(best),possible_maximizers=winners,source_files_sha256=pins,
    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    scope='For the fixed saved rule family and removed graph, these surviving cycles bound each minimum mean from above. Full-edge potentials are needed for matching lower bounds. Integer a,b only. Saturating b=120-4a dominates smaller b at fixed a.')
path = HERE/'data/coefficient-screen.json'
assert not path.exists()
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('BEST_CYCLE_UPPER_BOUND',best,'POSSIBLE_OUTER_COEFFICIENTS',winners)
for r in rows[24:]:
    print(r)
