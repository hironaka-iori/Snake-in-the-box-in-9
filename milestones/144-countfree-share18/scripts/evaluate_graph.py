"""Conditional full-graph test: proved odd-length pair9 and hypothetical six25.

Run without --worker. The parent records resource checks, logs and timeout status.
No result from this experiment alone is an actual-snake upper bound.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, sys, time
_home = Path(__file__).resolve().parents[1]
_cli = argparse.ArgumentParser()
_cli.add_argument('--label', default='share18-impact')
_cli.add_argument('--timeout', type=int, default=3600)
_cli.add_argument('--outer', type=int, default=24)
_cli.add_argument('--middle', type=int, default=24)
_cli.add_argument('--rules', default='../120-nine-transition-window/data/full-rules.json')
_cli.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
_args = _cli.parse_args()

def _checked_weak_exclusion():
    # This gate executes before resource allocation, output creation, or graph imports.
    root = _home.parents[1]
    proof_home = _home.parent / '140-five-cycle-window'
    completion_path = proof_home / 'data/proof-completion.json'
    raw = completion_path.read_bytes()
    completion = json.loads(raw)
    assert str(completion.get('status','')).startswith('PASS'), 'The weak exclusion is not complete'
    spec = completion['weak_actual_theorem']
    assert spec['checked'] is True
    assert spec['directions'] == [0,1,2,0,3,2]
    assert spec['bounds'] == [[3,3],[0,5],[4,4],[0,5],[3,3]]
    source = (root / spec['source']).resolve()
    receipt = (root / spec['receipt']).resolve()
    source.relative_to(proof_home.resolve())
    receipt.relative_to(proof_home.resolve())
    assert source.suffix == '.lean'
    source_raw, receipt_raw = source.read_bytes(), receipt.read_bytes()
    assert hashlib.sha256(source_raw).hexdigest() == spec['source_sha256']
    assert hashlib.sha256(receipt_raw).hexdigest() == spec['receipt_sha256']
    audit = json.loads(receipt_raw)
    assert audit['status'] == 'PASS'
    assert audit['source_sha256'] == spec['source_sha256']
    assert Path(audit['source']).resolve() == source
    theorem = spec['theorem']
    assert isinstance(theorem,str) and theorem.strip()
    assert re.search(r'\btheorem\s+'+re.escape(theorem.split('.')[-1])+r'\b',source_raw.decode('utf-8-sig'))
    pins = {completion_path.relative_to(root).as_posix(): hashlib.sha256(raw).hexdigest(),
            source.relative_to(root).as_posix(): spec['source_sha256'],
            receipt.relative_to(root).as_posix(): spec['receipt_sha256']}
    return dict(theorem=theorem, pins=pins)
try:
    _proof_gate_info = _checked_weak_exclusion()
except Exception as error:
    print(json.dumps(dict(status='NOT_STARTED_PROOF_GATE',reason=repr(error))),flush=True)
    raise SystemExit(2)

assert re.fullmatch(r'[A-Za-z0-9_-]+', _args.label), 'Label must be a simple directory name'
assert _args.timeout > 0 and _args.outer == _args.middle == 24
_folder = _home / 'data' / _args.label
_lock = _home / 'data' / 'fullgraph.lock'
def _save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')
def _resources(exclude):
    cmd = "$o=Get-CimInstance Win32_OperatingSystem; $p=@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^python' -and $_.CommandLine -match 'evaluate_(graph|pair|six_shapes)\\.py' } | Select-Object ProcessId,CommandLine); @{free_bytes=([long]$o.FreePhysicalMemory*1024); processes=$p} | ConvertTo-Json -Depth 4 -Compress"
    r = subprocess.run(['powershell.exe','-NoProfile','-Command',cmd], capture_output=True, text=True, check=True, timeout=30)
    value = json.loads(r.stdout)
    value['other_fullgraph_processes'] = [p for p in value.pop('processes') if int(p['ProcessId']) not in exclude]
    assert value['free_bytes'] >= 3 * 1024**3, 'At least3GiB free physical memory is required'
    assert not value['other_fullgraph_processes'], 'Another full-graph calculation is running'
    return value
if not _args.worker:
    try:
        _resources({os.getpid()})
    except AssertionError as gate:
        print(json.dumps(dict(status='NOT_STARTED_RESOURCE_GATE',reason=str(gate))),flush=True)
        raise SystemExit(0)
    _folder.mkdir(parents=True, exist_ok=False)
    _record = {'status':'PREPARING', 'label':_args.label, 'timeout_seconds':_args.timeout,
               'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    _record['proof_gate'] = _proof_gate_info
    _owned_lock = False
    _child = None
    try:
        _record['resources'] = _resources({os.getpid()})
        with _lock.open('x', encoding='utf-8') as f:
            json.dump({'parent_pid':os.getpid(), 'label':_args.label}, f)
        _owned_lock = True
        (_folder/'evaluate_graph.exact.py').write_bytes(Path(__file__).read_bytes())
        _command = [sys.executable, '-B', '-X', 'utf8', str(Path(__file__).resolve()), *sys.argv[1:], '--worker']
        with (_folder/'stdout.log').open('w',encoding='utf-8') as out, (_folder/'stderr.log').open('w',encoding='utf-8') as err:
            _env = os.environ.copy()
            _env['SNAKE144_GRAPH_PARENT_PID'] = str(os.getpid())
            _child = subprocess.Popen(_command, stdout=out, stderr=err, env=_env)
            _record.update(status='RUNNING', worker_pid=_child.pid, command=_command)
            _save(_folder/'run-status.json', _record)
            try:
                _code = _child.wait(timeout=_args.timeout)
            except subprocess.TimeoutExpired:
                _record['status'] = 'TIMEOUT'
                _save(_folder/'run-status.json', _record)
                subprocess.run(['taskkill.exe','/PID',str(_child.pid),'/T','/F'], capture_output=True, timeout=30)
                _child.wait(timeout=30)
                _code = None
            if _code is not None:
                _record['returncode'] = _code
                if _code == 0:
                    _result = json.loads((_folder/'results.json').read_text(encoding='utf-8'))
                    assert _result['status'] == 'PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
                    _record['status'] = 'PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
                else:
                    _record['status'] = 'FAILED'
    except BaseException as error:
        _record.update(status='TIMEOUT' if _record['status'] == 'TIMEOUT' else 'FAILED', error=repr(error))
        if _child is not None and _child.poll() is None:
            subprocess.run(['taskkill.exe','/PID',str(_child.pid),'/T','/F'], capture_output=True, timeout=30)
            _child.wait(timeout=30)
    finally:
        _record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        _save(_folder/'run-status.json', _record)
        if _owned_lock:
            _lock.unlink()
    print(json.dumps(_record, indent=2), flush=True)
    raise SystemExit(0 if _record['status'].startswith('PASS_') else 1)
_parent = int(os.environ['SNAKE144_GRAPH_PARENT_PID'])
assert json.loads(_lock.read_text(encoding='utf-8')) == {'parent_pid':_parent, 'label':_args.label}
_worker_resources = _resources({os.getpid(), _parent})
_save(_folder/'worker-resources.json', _worker_resources)
sys.argv = [sys.argv[0], '--outer', '24', '--middle', '24', '--rules', _args.rules, '--label', _args.label]

DERIVED_SOURCE_SHA256 = '066b117d63f3d6cf78341073fa7b7a09dd39946a7f4b77961bf71b23114e782f'
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
label = args.label or 'share18-impact'
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




# Reproduce all source pins for the proposed experiment before changing the graph.
task = read('milestones/130-fourth-count-large/data/next-pressure-task.json')
assert task['candidate_shape'] == '0123104'
assert task['candidate_six_count_floor'] == 25 and task['odd_length_pair_floor'] == 9
assert task['candidate_lean_proof_complete'] is False
for rel, digest in task['source_pins'].items():
    raw = (ROOT / rel).read_bytes()
    assert sha(raw) == digest, 'Task source changed: ' + rel
    pins[rel] = digest
for rel in ['milestones/131-odd-pair-six-count/scripts/prepare_graph.py',
            'milestones/124-six-count-cycle-pressure/scripts/evaluate_six_shapes.py',
            'milestones/121-replacement-window-pressure/scripts/evaluate_pair.py']:
    pins[rel] = sha((ROOT / rel).read_bytes())
assert pins['milestones/124-six-count-cycle-pressure/scripts/evaluate_six_shapes.py'] == DERIVED_SOURCE_SHA256

old_bonus24 = bonus.copy()
base_weights = {name: full_baselines[name] - old_bonus24 for name in full_baselines}
odd_reject = np.zeros(len(code), dtype=bool)
pair_bonus = np.zeros(len(code), dtype=np.int64)
pair_placements = []
for s in range(2):
    for reverse in [False, True]:
        rejected = np.zeros(len(code), dtype=bool)
        for di, word in enumerate(ds):
            selected = word[s+2:s+8]
            if reverse:
                selected = selected[::-1]
            if canon(selected) != (0,1,2,0,3,2):
                continue
            lo, hi = np.searchsorted(arrays['direction'], [di,di+1])
            five = digits[lo:hi,s:s+5]
            if reverse:
                five = five[:,::-1]
            a, b = five[:,1], five[:,3]
            rejected[lo:hi] = (a < 6) & (b < 6) & (a+b < 9)
            if s == 1:
                pair_bonus[lo:hi] = np.maximum(pair_bonus[lo:hi], 24*np.maximum(0,9-a-b))
        odd_reject |= rejected
        pair_placements.append(dict(placement=s, reverse=reverse,
            deleted_from121=int(np.count_nonzero(rejected & keep))))
# A separate shape-only computation checks both orientations and clipped semantics.
independent_pair_drop = np.zeros(len(code), dtype=bool)
independent_pair_bonus = np.zeros(len(code), dtype=np.int64)
for di, word in enumerate(ds):
    lo, hi = np.searchsorted(arrays['direction'], [di,di+1])
    for s in range(2):
        if shape(word[s+2:s+8]) != (0,1,2,0,3,2):
            continue
        a, b = digits[lo:hi,s+1], digits[lo:hi,s+3]
        independent_pair_drop[lo:hi] |= (a<6)&(b<6)&(a+b<9)
        if s == 1:
            independent_pair_bonus[lo:hi] = 24*np.maximum(0,9-a-b)
assert np.array_equal(odd_reject, independent_pair_drop)
assert np.array_equal(pair_bonus, independent_pair_bonus)

# Six-count shape recognition permits reversal; chronological count order is fixed.
target = shape((0,1,2,3,1,0,4))
six_match = np.array([shape(word[2:]) == target for word in ds])[arrays['direction']]
six_sum = digits.sum(axis=1)
six_guard = six_match & (digits[:,0] < 6)
six_reject = six_match & np.all(digits < 6,axis=1) & (six_sum < 25)
six_bonus = 24*np.where(six_guard, np.maximum(0,25-six_sum), 0)
assert np.all(~six_reject | six_guard)
shared = np.maximum(np.maximum(old_bonus24,pair_bonus),six_bonus)
mask = keep & ~odd_reject & ~six_reject

# Reproduce the immediate predecessor before applying any new rule.
previous131=read('milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json')
assert previous131['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
previous131_profiles={x['profile']:x for x in previous131['profiles']}
old_removed=read('milestones/131-odd-pair-six-count/data/odd-pair9-six25/removed-indices.json')
assert np.array_equal(np.flatnonzero(~mask),np.array(old_removed))
assert int(mask.sum())==previous131['edges']
for name in ['completed','conditional_floor18']:
    assert sha((base_weights[name]+shared)[mask].tobytes())==previous131_profiles[name]['weight_sha256']
for rel in ['milestones/138-seven-cycle-endpoints/data/proof-completion.json',
 'milestones/138-seven-cycle-endpoints/data/ActualBase138Minimal-audit.json',
 'milestones/138-seven-cycle-endpoints/lean/ActualBase138Minimal.lean',
 'milestones/137-actual-block-assembly/data/verification.json',
 'milestones/137-actual-block-assembly/data/ActualCount137-audit.json',
 'milestones/137-actual-block-assembly/lean/ActualCount137.lean',
 'milestones/138-seven-cycle-endpoints/data/Credit138-audit.json',
 'milestones/138-seven-cycle-endpoints/lean/Credit138.lean',
 'milestones/139-exclusion-occurrence-credit/scripts/prepare_graph.py']:
    pins[rel]=sha((ROOT/rel).read_bytes())
proof=read('milestones/138-seven-cycle-endpoints/data/proof-completion.json')
assert proof['status']=='PASS_ACTUAL_NINE_TRANSITION_EXCLUSION_AND_CONDITIONAL_ARITHMETIC'
assert sha((ROOT/'milestones/138-seven-cycle-endpoints/lean/ActualBase138Minimal.lean').read_bytes())==proof['final_source_sha256']
occurrences=read('milestones/137-actual-block-assembly/data/verification.json')
assert occurrences['checked_total_low_pair_window_bound']==24 and occurrences['actual_occurrence_bound_lean_checked']
old_mask=mask.copy()
new_shape=np.array([canon(word)==(0,1,2,3,0,1,4,3,0) for word in ds])[arrays['direction']]
new_reject=new_shape & np.all(digits==np.array([6,3,3,3,5,2]),axis=1)
mask &= ~new_reject
# Only exact stored counts may certify the low-pair event.
suffix_shape=np.array([shape(word[3:9])==(0,1,2,0,3,2) for word in ds])[arrays['direction']]
a,b=digits[:,2],digits[:,4]
event=suffix_shape & (a<6) & (b<6) & (a+b<=9)
assert not np.any(event & mask & (a+b<9))
assert old_mask[992157] and not mask[992157] and mask[1273862]
four_ids=np.array([e['edge'] for e in previous131_profiles['completed']['cycle']])
assert len(four_ids)==4 and np.all(mask[four_ids]) and int(event[four_ids].sum())==2


# Reproduce139 after all its exclusions and before the new weak exclusion.
previous139=read('milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/results.json')
assert previous139['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
assert sha((ROOT/'milestones/139-exclusion-occurrence-credit/scripts/evaluate_graph.py').read_bytes()) == 'c38a19a4e6288f8c1e88bbc9c004525527bc613339683157569c88f0d0e244c7'
previous139_profiles={p['profile']:p for p in previous139['profiles']}
previous139_removed=read('milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/removed-indices.json')
assert np.array_equal(np.flatnonzero(~mask),np.array(previous139_removed))
assert int(mask.sum())==previous139['edges']
for name in ['completed','conditional_floor18']:
    assert sha((3*(base_weights[name]+shared)+83*event)[mask].tobytes())==previous139_profiles[name]['weight_sha256']
previous139_mask=mask.copy()
pins.update(_proof_gate_info['pins'])
for extra in ['milestones/141-zero-credit-comparison/scripts/prepare_graph.py','milestones/141-zero-credit-comparison/data/preparation.json']:
    pins[extra]=sha((ROOT/extra).read_bytes())
for rel in ['milestones/139-exclusion-occurrence-credit/scripts/evaluate_graph.py',
            'milestones/140-five-cycle-window/scripts/prepare_graph.py',
            'milestones/140-five-cycle-window/data/graph-preparation.json']:
    pins[rel]=sha((ROOT/rel).read_bytes())
weak_reject=np.zeros(len(code),dtype=bool)
weak_placements=[]
for placement in range(2):
    for reverse in [False,True]:
        oriented=np.zeros(len(code),dtype=bool)
        for di,word in enumerate(ds):
            selected=word[placement+2:placement+8]
            if reverse:selected=selected[::-1]
            if canon(selected)!=(0,1,2,0,3,2):continue
            lo,hi=np.searchsorted(arrays['direction'],[di,di+1])
            five=digits[lo:hi,placement:placement+5]
            if reverse:five=five[:,::-1]
            oriented[lo:hi]=np.all(five<6,axis=1)&(five[:,0]==3)&(five[:,1]<=5)&(five[:,2]==4)&(five[:,3]<=5)&(five[:,4]==3)
        weak_reject |= oriented
        weak_placements.append(dict(placement=placement,reverse=reverse,total=int(oriented.sum()),on_predecessor139=int((oriented&previous139_mask).sum())))
# Separate palindrome recognition and explicit chronological columns check both placements.
independent_weak=np.zeros(len(code),dtype=bool)
for placement in range(2):
    recognized=np.array([shape(word[placement+2:placement+8])==(0,1,2,0,3,2) for word in ds])[arrays['direction']]
    five=digits[:,placement:placement+5]
    independent_weak |= recognized & np.all(five<6,axis=1) & (five[:,0]==3) & (five[:,2]==4) & (five[:,4]==3) & (five[:,1]<=5) & (five[:,3]<=5)
assert np.array_equal(weak_reject,independent_weak)
mask &= ~weak_reject
assert np.array_equal(mask,previous139_mask & ~weak_reject)
predecessor_cycle_checks=[]
for name,p in previous139_profiles.items():
    cycle_ids=np.array([e['edge'] for e in p['cycle']])
    assert np.all(previous139_mask[cycle_ids])
    killed=[int(k) for k in cycle_ids if weak_reject[k]]
    predecessor_cycle_checks.append(dict(profile=name,removed=killed,survives=not killed))
    if name=='completed':assert set(killed)=={308566,3806548}
    else:assert not killed

# Reproduce the immediate zero-credit predecessor before changing weights.
previous141=read('milestones/141-zero-credit-comparison/data/five-cycle-zero/results.json')
assert previous141['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
previous141_profiles={p['profile']:p for p in previous141['profiles']}
previous141_removed=read('milestones/141-zero-credit-comparison/data/five-cycle-zero/removed-indices.json')
assert np.array_equal(np.flatnonzero(~mask),np.array(previous141_removed))
assert int(mask.sum())==previous141['edges']
for name in ['completed','conditional_floor18']:
    assert sha((base_weights[name]+shared)[mask].tobytes())==previous141_profiles[name]['weight_sha256']
for rel in ['milestones/142-retuned-occurrence-credit/scripts/prepare_graph.py',
            'milestones/142-retuned-occurrence-credit/data/preparation.json',
            'milestones/141-zero-credit-comparison/data/next-credit.json',
            'milestones/141-zero-credit-comparison/data/Comparison141-audit.json']:
    pins[rel]=sha((ROOT/rel).read_bytes())
seven_ids=np.array([e['edge'] for e in previous141_profiles['completed']['cycle']])
assert np.all(mask[seven_ids]) and len(seven_ids)==7 and int(event[seven_ids].sum())==2
assert Fraction(int((12*(base_weights['completed']+shared)+533*event)[seven_ids].sum()),12*7)==Fraction(3011,6)

ids = np.flatnonzero(mask)
u, v = arrays['U'][mask], arrays['V'][mask]
(folder/'removed-indices.json').write_text(json.dumps(np.flatnonzero(~mask).tolist())+'\n',encoding='utf-8')

# Historical18-cycle comparison is checked in the reproduced139 predecessor graph.
saved = previous121_profiles['completed']['cycle']
assert len(saved) == 18
saved_ids = np.array([e['edge'] for e in saved])
assert np.all(previous139_mask[saved_ids])
assert np.all(mask[saved_ids])
saved_mean = Fraction(int((base_weights['completed']+shared)[saved_ids].sum()),18)
assert saved_mean == Fraction(3011,6), 'Saved18-cycle comparison changed'
assert not np.any(event[saved_ids])
assert Fraction(int((3*(base_weights['completed']+shared)+83*event)[four_ids].sum()),12)==Fraction(3011,6)
assert np.array_equal(previous139_mask,old_mask & ~new_reject)

pool = np.flatnonzero(alg['prune'](N,u,v))
assert len(pool) > 0, 'No cyclic core remains'
active = np.unique(np.concatenate([u[pool],v[pool]]))
index = np.full(N,-1,dtype=np.int32)
index[active] = np.arange(len(active))
# Change only the012034 count-free floor after every predecessor check.
share_shape=np.array([shape(word[-6:])==(0,1,2,0,3,4) for word in ds])[arrays['direction']]
last_count=digits[:,-1].astype(np.int64)
share_delta=np.where(share_shape,
    np.maximum(arrays['weight'],120*last_count+18)-np.maximum(arrays['weight'],120*last_count),0)
profile_base=base_weights['completed']+share_delta
assert np.all(profile_base[share_shape]==base_weights['conditional_floor18'][share_shape])
assert np.all(profile_base[~share_shape]==base_weights['completed'][~share_shape])
assert np.all(profile_base<=base_weights['conditional_floor18'])
for rel in ['milestones/144-countfree-share18/scripts/prepare_graph.py',
            'milestones/144-countfree-share18/data/graph-preparation.json',
            'milestones/144-countfree-share18/data/alternative-review.json']:
    pins[rel]=sha((ROOT/rel).read_bytes())
profiles = []
for name in ['completed']:
    before = time.monotonic()
    W = (profile_base+shared)[mask]
    _, cy = alg['howard'](len(active),index[u[pool]],index[v[pool]],W[pool],iters=400)
    ci = pool[np.asarray(cy,dtype=np.int64)]
    assert len(ci) > 0
    assert np.array_equal(v[ci],np.roll(u[ci],-1))
    mu = Fraction(sum(int(x) for x in W[ci]),len(ci))
    p, d = mu.numerator, mu.denominator
    # Establish conservative int64 safety for every possible relaxation below.
    step_bound = abs(p)+d*max(abs(int(W.min())),abs(int(W.max())))
    assert 1503*step_bound < 2**62
    dist = np.zeros(N,dtype=np.int64)
    for iteration in range(1,1501):
        nxt = dist.copy()
        np.minimum.at(nxt,v,dist[u]+d*W-p)
        if np.array_equal(nxt,dist):
            break
        dist = nxt
    else:
        raise AssertionError('Potential did not converge; no exact minimum certified')
    slack = d*W + dist[u] - p - dist[v]
    assert np.all(slack >= 0), 'An all-edge potential inequality failed'
    assert np.all(slack[ci] == 0), 'The reported cycle does not attain the certificate'
    pi = dist-dist.min()
    R = int(pi.max())
    buf = pi.astype('<i8').tobytes()
    filename = name+'-potential.i64.gz'
    (folder/filename).write_bytes(gzip.compress(buf,mtime=0))
    bound = Fraction(1098960*d+8*p+R,4200*d+p)
    cycle = []
    for e in ci:
        k = int(ids[e])
        cycle.append(dict(edge=k,u=int(u[e]),v=int(v[e]),direction=int(arrays['direction'][k]),
            history=int(arrays['history'][k]),count_code=int(code[k]),directions=ds[int(arrays['direction'][k])],
            counts=digits[k].tolist(),weight=int(W[e]),base_weight=int(base_weights[name][k]),
            weight_multiplier=1,occurrence_event=bool(event[k]),occurrence_credit_scaled=0,
            countfree_012034_bonus=int(share_delta[k]),
            old_bonus24=int(old_bonus24[k]),pair_bonus24=int(pair_bonus[k]),six_bonus24=int(six_bonus[k]),
            shared_bonus=int(shared[k]),six_shape_matches=bool(six_match[k]),six_guard=bool(six_guard[k])))
    row = dict(profile='completed_plus_012034_share18_pending',mean=str(mu),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,
        weight_multiplier=1,credit='0',occurrence_allowance=24,
        target_mean_reached=mu>=496,target_range_reached=Fraction(R,d)<632,
        cycle_attaining=True,weight_sha256=sha(W.tobytes()),potential_file=filename,potential_sha256=sha(buf),
        all_edge_inequalities_checked=True,inequalities_checked=len(W),minimum_slack=int(slack.min()),
        iterations=iteration,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,
        zero_range_comparison=str(Fraction(1098960*d+8*p,4200*d+p)),seconds=time.monotonic()-before)
    profiles.append(row)
    (folder/(name+'-profile.json')).write_text(json.dumps(row,indent=2)+'\n',encoding='utf-8')
    print(name,'exact mean',mu,'range',Fraction(R,d),'conditional comparison',bound,flush=True)
assert all(sha((ROOT/rel).read_bytes()) == digest for rel,digest in pins.items())
out = dict(status='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA',profiles=profiles,states=N,edges=len(ids),
    coefficients=coefficients,rules=rules,inherited_pair_guards=pair_guards,
    predecessor131_reproduced=True,predecessor131_edges=int(old_mask.sum()),
    predecessor139_reproduced=True,predecessor139_edges=int(previous139_mask.sum()),
    predecessor141_reproduced=True,predecessor141_edges=previous141['edges'],
    retained_additional_profile_source='milestones/141-zero-credit-comparison/data/five-cycle-zero/results.json',
    new_weak_exclusion=dict(directions=[0,1,2,0,3,2],bounds=[[3,3],[0,5],[4,4],[0,5],[3,3]],
        checked_theorem=_proof_gate_info['theorem'],proof_pins=_proof_gate_info['pins'],
        total=int(weak_reject.sum()),removed_from139=int((weak_reject&previous139_mask).sum()),
        placements=weak_placements,independent_recognition_agrees=True),
    predecessor139_cycle_checks=predecessor_cycle_checks,
    new_full_nine_rejections_total=int(new_reject.sum()),
    new_full_nine_rejections_on_predecessor=int((new_reject&old_mask).sum()),
    occurrence_events_retained=int(event[mask].sum()),weight_multiplier=1,
    credit='0',occurrence_allowance=24,
    added_share_floor=dict(shape=[0,1,2,0,3,4],floor=18,actual_lean_theorem_complete=False,changed_retained_edges=int(np.count_nonzero(share_delta[mask]))),
    event_rule='Suffix012032, both pair symbols below6, sum at most9; prefix representations never counted.',
    new_exclusion_rule='Forward full-nine012301430 with symbols6,3,3,3,5,2; no reversal of missing count data.',

    baseline121_weight_hashes_reproduced=True,baseline121_removals_reproduced=True,
    baseline121_edges=int(keep.sum()),pair_deleted_from121=int(np.count_nonzero(odd_reject&keep)),
    six_deleted_from121=int(np.count_nonzero(six_reject&keep)),
    six_deleted_after_pair=int(np.count_nonzero(six_reject&keep&~odd_reject)),
    new_removed=int(np.count_nonzero(keep&~mask)),pair_placements=pair_placements,
    pair_credit_improvements=int(np.count_nonzero((pair_bonus>old_bonus24)&mask)),
    six_credit_improvements=int(np.count_nonzero((six_bonus>np.maximum(old_bonus24,pair_bonus))&mask)),
    shared_bonus_is_maximum=True,old_bonus_preserved=True,odd_length_pair_floor=9,
    six_count_hypothesis=dict(shape=list(target),floor=25,lean_proof_complete=False,native_status='UNSAT_UNCERTIFIED',
        guard='First chronological symbol below6; reversal changes only shape recognition',deletion='All six symbols exact and sum below25'),
    inherited_hypotheses='All prior count-sum, hypothetical six-floor25 and odd-length pair assumptions remain. Only012034 share18 is added to completed shares; its actual Lean theorem remains pending. No other pending count-free floor is added.',
    saved18_cycle_hypothetical_mean=str(saved_mean),saved18_checked_in='predecessor139',source_files_sha256=pins,algorithm_sha256=algsha,
    script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
    scope='The added012034 share18 is still a local hypothesis. Exact finite-graph minima under stated hypotheses. Pair9 applies to odd-length actual snakes, including235. Six25 is hypothetical. Full graph-to-snake assembly remains pending. Execution was gated on the checked weak five-count exclusion; the earlier exclusion and occurrence allowance remain inherited. Other local hypotheses and graph assembly remain pending. No new actual-snake upper bound is claimed.')
(folder/'results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
