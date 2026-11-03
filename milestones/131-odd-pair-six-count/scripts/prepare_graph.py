"""Generate the bounded milestone131 experiment; this script never loads the graph."""
from pathlib import Path
import ast
import hashlib
import itertools
import json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
SOURCE = ROOT / 'milestones/124-six-count-cycle-pressure/scripts/evaluate_six_shapes.py'
sha = lambda b: hashlib.sha256(b).hexdigest()

WRAPPER = r'''"""Conditional full-graph test: proved odd-length pair9 and hypothetical six25.

Run without --worker. The parent records resource checks, logs and timeout status.
No result from this experiment alone is an actual-snake upper bound.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, sys, time
_home = Path(__file__).resolve().parents[1]
_cli = argparse.ArgumentParser()
_cli.add_argument('--label', default='odd-pair9-six25')
_cli.add_argument('--timeout', type=int, default=3600)
_cli.add_argument('--outer', type=int, default=24)
_cli.add_argument('--middle', type=int, default=24)
_cli.add_argument('--rules', default='../120-nine-transition-window/data/full-rules.json')
_cli.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
_args = _cli.parse_args()
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
    _folder.mkdir(parents=True, exist_ok=False)
    _record = {'status':'PREPARING', 'label':_args.label, 'timeout_seconds':_args.timeout,
               'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
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
            _env['SNAKE131_PARENT_PID'] = str(os.getpid())
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
_parent = int(os.environ['SNAKE131_PARENT_PID'])
assert json.loads(_lock.read_text(encoding='utf-8')) == {'parent_pid':_parent, 'label':_args.label}
_worker_resources = _resources({os.getpid(), _parent})
_save(_folder/'worker-resources.json', _worker_resources)
sys.argv = [sys.argv[0], '--outer', '24', '--middle', '24', '--rules', _args.rules, '--label', _args.label]
'''

SUFFIX = r'''
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
ids = np.flatnonzero(mask)
u, v = arrays['U'][mask], arrays['V'][mask]
(folder/'removed-indices.json').write_text(json.dumps(np.flatnonzero(~mask).tolist())+'\n',encoding='utf-8')

# Cross-check the saved completed18-cycle comparison without mistaking it for a minimum.
saved = previous121_profiles['completed']['cycle']
assert len(saved) == 18
saved_ids = np.array([e['edge'] for e in saved])
assert np.all(mask[saved_ids])
saved_mean = Fraction(int((base_weights['completed']+shared)[saved_ids].sum()),18)
assert saved_mean == Fraction(3011,6), 'Saved18-cycle comparison changed'

pool = np.flatnonzero(alg['prune'](N,u,v))
assert len(pool) > 0, 'No cyclic core remains'
active = np.unique(np.concatenate([u[pool],v[pool]]))
index = np.full(N,-1,dtype=np.int32)
index[active] = np.arange(len(active))
profiles = []
for name in ['completed','conditional_floor18']:
    before = time.monotonic()
    W = (base_weights[name]+shared)[mask]
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
            old_bonus24=int(old_bonus24[k]),pair_bonus24=int(pair_bonus[k]),six_bonus24=int(six_bonus[k]),
            shared_bonus=int(shared[k]),six_shape_matches=bool(six_match[k]),six_guard=bool(six_guard[k])))
    row = dict(profile=name,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,
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
    inherited_hypotheses='All121 count-sum assumptions remain inherited; conditional_floor18 also retains its additional floor assumptions.',
    saved18_cycle_hypothetical_mean=str(saved_mean),source_files_sha256=pins,algorithm_sha256=algsha,
    script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
    scope='Exact finite-graph minima under stated hypotheses. Pair9 applies to odd-length actual snakes, including235. Six25 is hypothetical. Full graph-to-snake assembly remains pending. No new unconditional or conditional actual-snake upper bound is claimed.')
(folder/'results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
'''

def main():
    raw = SOURCE.read_bytes()
    source = raw.decode('utf-8-sig')
    marker = 'old_bonus24=bonus.copy()'
    assert source.count(marker) == 1
    prefix = source.split(marker)[0]
    prefix = prefix[prefix.index('from pathlib import Path'):]
    prefix = prefix.replace("label = args.label or 'graph-26-25-25'", "label = args.label or 'odd-pair9-six25'")
    assert 'assert sha(full_baselines[name][keep].tobytes())==previous121_profiles[name]' in prefix
    assert 'assert np.array_equal(removed,np.array(previous121_removed))' in prefix
    generated = WRAPPER + '\nDERIVED_SOURCE_SHA256 = ' + repr(sha(raw)) + '\n' + prefix + SUFFIX
    ast.parse(generated)
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    # Exhaustively check the pair deletion and deficit on actual values1..21.
    cases = 0
    for a,b in itertools.product(range(1,22),repeat=2):
        x,y = min(a,6),min(b,6)
        rejected = x < 6 and y < 6 and x+y < 9
        assert not rejected or a+b < 9
        if a+b >= 9:
            assert max(0,9-x-y) <= (a-x)+(b-y)
        assert rejected == (y < 6 and x < 6 and y+x < 9)
        cases += 1
    # Six guards must retain chronological first position even under reversal.
    six_cases = 0
    for counts in itertools.product(range(1,7),repeat=6):
        guard = counts[0] < 6
        reject = all(x < 6 for x in counts) and sum(counts) < 25
        assert not reject or guard
        bonus = 24*max(0,25-sum(counts)) if guard else 0
        assert bonus >= 0
        assert max(7,11,bonus) >= max(7,11)
        six_cases += 1
    target = HERE / 'scripts/evaluate_graph.py'
    target.write_text(generated,encoding='utf-8',newline='\n')
    note = dict(status='PREPARED_NOT_EXECUTED',source_derivation=SOURCE.relative_to(ROOT).as_posix(),
        source_sha256=sha(raw),prepare_sha256=sha(Path(__file__).read_bytes()),evaluate_sha256=sha(target.read_bytes()),
        baseline='The inherited124 reconstruction is retained through its121 removal and full-weight hash assertions.',
        profiles=['completed','conditional_floor18'],odd_length_pair_floor=9,hypothetical_six_shape='0123104',hypothetical_six_floor=25,
        checks_run=dict(ast_parsed_both_scripts=True,actual_pair_cases=cases,clipped_six_cases=six_cases),
        checks_not_run=['full graph loading','baseline121 reconstruction','minimum cycle mean','all-edge potential certificate','Lean','SAT'],
        runtime=dict(minimum_free_memory_bytes=3*1024**3,duplicate_process_check=True,exclusive_lock=True,default_timeout_seconds=3600,
            timeout_and_failure_records_preserved=True,exact_script_snapshot=True,all_edge_potential_check=True,attaining_cycle_check=True),
        saved18_cycle_reference='3011/6, checked at experiment runtime only',
        scope='Preparation only. Both profiles retain their inherited hypotheses and the six-count floor remains hypothetical. No bound is obtained by preparing these scripts.')
    (HERE/'data').mkdir(exist_ok=True)
    (HERE/'data/preparation-note.json').write_text(json.dumps(note,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(note,indent=2))

if __name__ == '__main__':
    main()
