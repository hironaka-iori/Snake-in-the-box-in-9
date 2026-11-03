"""One bounded endpoint0 sharpness test. Preserve every model and validated cycle cut."""
from pathlib import Path
from itertools import combinations
import argparse, datetime, hashlib, json, os, re, subprocess, sys, time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def save(path,value):
    temp = path.with_name(path.name+'.pending')
    temp.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
    temp.replace(path)
def resources(exclude):
    command = "$o=Get-CimInstance Win32_OperatingSystem; $p=@(Get-CimInstance Win32_Process | Where-Object {$_.Name -match '^python' -and $_.CommandLine -match '133-endpoint-occurrences' -and $_.CommandLine -match 'probe\\.py'} | Select-Object ProcessId,CommandLine); @{free_bytes=([long]$o.FreePhysicalMemory*1024); processes=$p} | ConvertTo-Json -Compress -Depth 4"
    value = json.loads(subprocess.check_output(['powershell.exe','-NoProfile','-Command',command],text=True,timeout=30))
    value['other_runs'] = [p for p in value.pop('processes') if int(p['ProcessId']) not in exclude]
    assert value['free_bytes'] >= 1610612736, 'At least1.5GiB free physical memory is required'
    assert not value['other_runs'], 'Another instance is running'
    return value
def verify_sources(preparation):
    assert sha(H/'work/probe-endpoint0/base.cnf') == preparation['cnf_sha256']
    assert sha(H/'data/encoding.json') == preparation['encoding_sha256']
    for rel,digest in preparation['source_files_sha256'].items():
        assert sha(R/rel) == digest, 'Source changed: '+rel
def cnf_bytes(nv,clauses):
    return (f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode('ascii')
def write_cnf(path,nv,clauses):
    temporary = path.with_name(path.name+'.pending')
    temporary.write_bytes(cnf_bytes(nv,clauses))
    temporary.replace(path)

def worker(folder,preparation,parent):
    save(folder/'worker-resources.json',resources({os.getpid(),parent}))
    verify_sources(preparation)
    sys.dont_write_bytecode = True
    sys.path[:0] = [str(R/'work/share_packages'),str(R/'work/solver_packages')]
    from pysat.solvers import Cadical153
    metadata = json.loads((H/'data/encoding.json').read_text(encoding='utf-8'))
    lines = (H/'work/probe-endpoint0/base.cnf').read_text(encoding='ascii').splitlines()
    header = lines[0].split()
    nv,nc = int(header[2]),int(header[3])
    clauses = []
    for line in lines[1:]:
        values = [int(x) for x in line.split()]
        assert values[-1] == 0
        clauses.append(values[:-1])
    assert len(clauses) == nc == metadata['clauses'] and nv == metadata['variables']
    assert cnf_bytes(nv,clauses) == (H/'work/probe-endpoint0/base.cnf').read_bytes()
    common = [v for v in range(512) if (v^3).bit_count() == (v^6).bit_count() == 2]
    assert common == metadata['common_sphere'] and len(common) == 14
    state = dict(status='RUNNING',calls=0,models=0,cycle_cuts=[],nominal_seconds=45,conflicts_per_call=1000,
        cnf_sha256=preparation['cnf_sha256'],preparation_sha256=sha(H/'data/preparation.json'),
        source_files_sha256=preparation['source_files_sha256'],script_sha256=sha(Path(__file__)))
    state_path = folder/'worker-status.json'
    save(state_path,state)
    save(folder/'cycle-cuts.json',[])
    write_cnf(folder/'current.cnf',nv,clauses)
    begin = time.monotonic()
    with Cadical153(bootstrap_with=clauses) as solver:
        while time.monotonic()-begin < 45:
            solver.conf_budget(1000)
            answer = solver.solve_limited()
            state['calls'] += 1
            state['seconds'] = time.monotonic()-begin
            save(state_path,state)
            if answer is None:
                continue
            if answer is False:
                state['status'] = 'UNSAT_UNCERTIFIED'
                break
            raw = solver.get_model()
            state['models'] += 1
            number = state['models']
            save(folder/f'raw-model-{number:04d}.json',raw)
            assignment = {abs(x):x>0 for x in raw}
            assert len(assignment) == len(raw) and all(i in assignment for i in range(1,nv+1))
            assert all(any(assignment[abs(lit)] == (lit>0) for lit in clause) for clause in clauses)
            selected = {v for v in range(512) if assignment[1+v]}
            flags = {v for v in range(512) if assignment[513+v]}
            adjacency = {v:sorted(v^(1<<d) for d in range(9) if v^(1<<d) in selected) for v in selected}
            assert set(metadata['window']) <= selected
            assert all(len(ns) in [1,2] for ns in adjacency.values())
            assert flags == {v for v,ns in adjacency.items() if len(ns) == 1}
            assert len(flags) == 2 and {v.bit_count()%2 for v in flags} == {0,1}
            assert 0 in flags and assignment[513]
            unseen,components = set(selected),[]
            while unseen:
                frontier = [min(unseen)]
                component = set()
                while frontier:
                    vertex = frontier.pop()
                    if vertex in component:
                        continue
                    component.add(vertex)
                    frontier.extend(w for w in adjacency[vertex] if w not in component)
                unseen -= component
                components.append(sorted(component))
            cycles = [c for c in components if all(len(adjacency[v]) == 2 for v in c)]
            save(folder/f'selected-{number:04d}.json',dict(selected=sorted(selected),endpoint_flags=sorted(flags),components=components,cycles=cycles))
            if cycles:
                for cut in cycles:
                    cutset = set(cut)
                    assert cut and len(cut) == len(cutset)
                    assert all(sum(v^(1<<d) in cutset for d in range(9)) >= 2 for v in cut)
                    assert cut not in state['cycle_cuts']
                    state['cycle_cuts'].append(cut)
                    clause = [-(1+v) for v in cut]
                    clauses.append(clause)
                    # Persist the cut and its exact input before asserting it to the solver.
                    save(folder/'cycle-cuts.json',state['cycle_cuts'])
                    write_cnf(folder/'current.cnf',nv,clauses)
                    save(state_path,state)
                    solver.add_clause(clause)
                continue
            assert len(components) == 1
            path,previous,current = [],None,min(flags)
            while True:
                assert current not in path
                path.append(current)
                onward = [v for v in adjacency[current] if v != previous]
                if not onward:
                    break
                assert len(onward) == 1
                previous,current = current,onward[0]
            assert len(path) == len(selected) and set(path) == selected
            assert {path[0],path[-1]} == flags and (len(path)-1)%2 == 1
            expected = metadata['window']
            def find_window(sequence):
                return next((r for r in range(len(sequence)-6) if sequence[r:r+7] == expected),None)
            r = find_window(path)
            if r is None:
                path.reverse()
                r = find_window(path)
            assert r is not None and r+6 < len(path)
            directions = [(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
            assert directions[r:r+6] == [0,1,2,0,3,2]
            pairs_checked = 0
            for i,v in enumerate(path):
                assert 0 <= v < 512
                for j in range(i+1,len(path)):
                    assert ((v^path[j]).bit_count() == 1) == (j == i+1)
                    pairs_checked += 1
            counts = []
            for offset in range(1,6):
                k = r+offset
                used = {directions[k-1],directions[k]}
                assert len(used) == 2
                allowed = [(a,b) for a,b in combinations(range(9),2) if a not in used and b not in used]
                corners = [path[k]^(1<<a)^(1<<b) for a,b in allowed]
                absent = [v for v in corners if v not in selected]
                direct = sum(path[k]^(1<<a) not in selected and path[k]^(1<<b) not in selected
                    and path[k]^(1<<a)^(1<<b) not in selected for a,b in combinations(range(9),2))
                assert len(corners) == 21 and direct == len(absent)
                counts.append(dict(index=k,vertex=path[k],allowed_pairs=allowed,opposite_corners=corners,
                    absent_corners=absent,alpha=len(absent),endpoint_distances=[(path[k]^path[0]).bit_count(),(path[k]^path[-1]).bit_count()]))
            pair = counts[1]['alpha']+counts[3]['alpha']
            assert pair <= 9
            assert path[0] == 0 and r == 0 and 0 in flags
            witness = dict(status='ACTUAL_ODD_ENDPOINT0_PATH_CHECKED',ordered_path=path,selected_vertices=sorted(selected),
                edges=len(path)-1,endpoint_flags=sorted(flags),window_start=r,window=expected,directions=directions,
                counts=counts,pair_sum=pair,sharpness_attained=(pair == 9),common_sphere=common,unordered_pairs_checked=pairs_checked,
                raw_model_file=f'raw-model-{number:04d}.json',all_current_clauses_checked=True,
                scope='Independently checked odd induced path starting at window0. Pair sum is computed directly; equality9 attains the known odd-length lower bound. No Lean witness check or global bound is claimed.')
            save(folder/'actual-path.json',witness)
            state['status'] = 'ACTUAL_ODD_ENDPOINT0_PATH_CHECKED'
            break
        else:
            state['status'] = 'UNKNOWN'
    if state['status'] == 'RUNNING':
        state['status'] = 'UNKNOWN'
    write_cnf(folder/'final.cnf',nv,clauses)
    verify_sources(preparation)
    state.update(seconds=time.monotonic()-begin,clauses=len(clauses),final_cnf_sha256=sha(folder/'final.cnf'),
        scope='One bounded sharpness test. Native UNSAT is uncertified. UNKNOWN or timeout gives no exclusion. Every added cycle cut is saved and checked to be nonempty, duplicate-free and of minimum internal degree at least2.')
    save(state_path,state)
    print(json.dumps(state,indent=2),flush=True)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--label',default='endpoint0',choices=['endpoint0'])
    ap.add_argument('--worker',action='store_true',help=argparse.SUPPRESS)
    args = ap.parse_args()
    assert re.fullmatch(r'[A-Za-z0-9_-]+',args.label)
    folder = H/'work'/('probe-'+args.label)
    lock = folder/'probe.lock'
    preparation = json.loads((H/'data/preparation.json').read_text(encoding='utf-8'))
    if args.worker:
        parent = int(os.environ['SNAKE133_PARENT_PID'])
        assert json.loads(lock.read_text()) == dict(parent_pid=parent,label=args.label)
        worker(folder,preparation,parent)
        return
    folder.mkdir(exist_ok=True)
    assert {p.name for p in folder.iterdir()} == {'base.cnf'}, 'Preserve the first probe; no automatic restart'
    state = dict(status='PREPARING',nominal_solver_seconds=45,hard_timeout_seconds=90,
        started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),script_sha256=sha(Path(__file__)))
    child,owned = None,False
    try:
        verify_sources(preparation)
        state['resources'] = resources({os.getpid()})
        with lock.open('x',encoding='utf-8') as f:
            json.dump(dict(parent_pid=os.getpid(),label=args.label),f)
        owned = True
        (folder/'probe.exact.py').write_bytes(Path(__file__).read_bytes())
        (folder/'prepare.exact.py').write_bytes((H/'scripts/prepare.py').read_bytes())
        (folder/'initial.cnf').write_bytes((H/'work/probe-endpoint0/base.cnf').read_bytes())
        env = os.environ.copy()
        env['SNAKE133_PARENT_PID'] = str(os.getpid())
        command = [sys.executable,'-B','-X','utf8',str(Path(__file__).resolve()),'--label',args.label,'--worker']
        with (folder/'stdout.log').open('w',encoding='utf-8') as out,(folder/'stderr.log').open('w',encoding='utf-8') as err:
            child = subprocess.Popen(command,stdout=out,stderr=err,env=env)
            state.update(status='RUNNING',worker_pid=child.pid,command=command)
            save(folder/'run-status.json',state)
            try:
                code = child.wait(timeout=90)
                state['returncode'] = code
                if code == 0:
                    result = json.loads((folder/'worker-status.json').read_text())
                    assert result['status'] in ['UNKNOWN','UNSAT_UNCERTIFIED','ACTUAL_ODD_ENDPOINT0_PATH_CHECKED']
                    state['status'] = result['status']
                else:
                    state['status'] = 'FAILED'
            except subprocess.TimeoutExpired:
                state['status'] = 'TIMEOUT'
                save(folder/'run-status.json',state)
                subprocess.run(['taskkill.exe','/PID',str(child.pid),'/T','/F'],capture_output=True,timeout=15)
                child.wait(timeout=15)
    except BaseException as error:
        state.update(status='TIMEOUT' if state['status']=='TIMEOUT' else 'FAILED',error=repr(error))
        if child is not None and child.poll() is None:
            child.kill()
            child.wait(timeout=15)
    finally:
        state['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        state['preserved_files_sha256'] = {p.name:sha(p) for p in folder.iterdir() if p.is_file() and p.name!='run-status.json'}
        save(folder/'run-status.json',state)
        if owned:
            lock.unlink()
    print(json.dumps(state,indent=2),flush=True)
    raise SystemExit(1 if state['status'] in ['FAILED','TIMEOUT'] else 0)

if __name__ == '__main__':
    main()
