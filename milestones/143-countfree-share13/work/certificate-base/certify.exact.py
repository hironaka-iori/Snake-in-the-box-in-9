"""One bounded native proof run, dependency trimming and independent ordered RUP replay."""
from pathlib import Path
import datetime, hashlib, importlib.util, json, os, subprocess, sys, time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
W = H/'work/certificate-base'
RECORD = H/'data/native-base.json'
REVIEW = H/'audit/native-base.md'
EXE = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
EXE_SHA = '4fb5f4f94a3632c185ea763f7da627d40038cca38d9481952d00d04cc881c94f'
TRIMMER = R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))

def save(path,value):
    temp = path.with_name(path.name+'.pending')
    temp.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
    temp.replace(path)

def formula(path):
    rows = path.read_text(encoding='ascii').splitlines()
    header = rows[0].split()
    assert header[:2] == ['p','cnf'] and len(header) == 4
    nv,nc = map(int,header[2:])
    clauses = []
    for row in rows[1:]:
        values = [int(x) for x in row.split()]
        assert values and values[-1] == 0 and all(0 < abs(x) <= nv for x in values[:-1])
        clauses.append(values[:-1])
    assert len(clauses) == nc
    exact = (f'p cnf {nv} {nc}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode('ascii')
    assert exact == path.read_bytes()
    return nv,clauses

def replay(path,original,core_ids,expected_lemmas,expected_hints):
    """Replay positive hints directly; preserve original clauses and their original IDs."""
    db = {cid:list(original[cid-1]) for cid in core_ids}
    assert list(db) == sorted(set(core_ids)) and all(1 <= cid <= len(original) for cid in core_ids)
    previous = len(original)
    lemmas = hints = literal_occurrences = 0
    final_empty = False
    used_original = set()
    maximum_hints = 0
    begin = time.monotonic()
    with path.open(encoding='ascii') as stream:
        for line in stream:
            values = [int(x) for x in line.split()]
            assert values and values[-1] == 0
            zero = values.index(0,1)
            cid,clause,hs = values[0],values[1:zero],values[zero+1:-1]
            assert cid > previous and cid not in db and all(0 < h < cid for h in hs)
            previous = cid
            hints += len(hs)
            assert hints <= 2000000, 'Hint limit exceeded during replay'
            maximum_hints = max(maximum_hints,len(hs))
            assignment = {}
            contradiction = False
            for lit in clause:
                variable,value = abs(lit),lit<0
                if variable in assignment and assignment[variable] != value:
                    contradiction = True
                assignment[variable] = value
            for position,hint in enumerate(hs):
                assert hint in db, ('Missing original or earlier derived clause',cid,hint)
                if hint <= len(original):
                    used_original.add(hint)
                if contradiction:
                    # Remaining hints are checked for valid IDs but cannot alter an existing contradiction.
                    continue
                unassigned = set()
                satisfied = False
                for lit in db[hint]:
                    value = assignment.get(abs(lit))
                    if value is None:
                        unassigned.add(lit)
                    elif value == (lit>0):
                        satisfied = True
                assert not satisfied, ('Satisfied hint is not a unit/conflict step',cid,hint)
                assert len(unassigned) <= 1, ('Nonunit hint',cid,hint,len(unassigned))
                if not unassigned:
                    contradiction = True
                else:
                    unit = next(iter(unassigned))
                    assignment[abs(unit)] = unit>0
            assert contradiction, ('RUP failed',cid)
            db[cid] = list(clause)
            lemmas += 1
            literal_occurrences += len(clause)
            final_empty = not clause
    assert final_empty and lemmas == expected_lemmas and hints == expected_hints
    assert used_original == set(core_ids)
    return dict(status='PASS_COMPLETE_NATIVE_RUP_REPLAY',lemmas=lemmas,hints=hints,
        derived_literal_occurrences=literal_occurrences,max_step_hints=maximum_hints,
        original_ids_preserved=True,original_clause_literal_multiplicity_preserved=True,
        every_trimmed_step_checked=True,final_empty_clause_checked=True,core_inputs_used=len(core_ids),
        seconds=time.monotonic()-begin)

def main():
    assert not RECORD.exists() and not REVIEW.exists() and not W.exists(), 'Preserve any previous attempt; no automatic restart'
    gate=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',
        "$o=Get-CimInstance Win32_OperatingSystem; @{free_bytes=([long]$o.FreePhysicalMemory*1024)} | ConvertTo-Json -Compress"],text=True))
    if gate['free_bytes']<1610612736:
        print(json.dumps(dict(status='NOT_STARTED_RESOURCE_GATE',resources=gate)));return
    W.mkdir(parents=True)
    (H/'audit').mkdir(exist_ok=True)
    out = dict(status='PREPARING',started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        script_sha256=sha(Path(__file__)),solver_timeout_seconds=60,replay_hint_limit=2000000,
        solver_runs=0,lean_export_started=False,lean_started=False)
    proc = None
    try:
        encoding = read(H/'work/short/encoding.json')
        source = H/'work/short/base.cnf'
        assert sha(source)==encoding['cnf_sha256']
        for rel,digest in encoding['source_files_sha256'].items():assert sha(R/rel)==digest,rel
        assert sha(EXE)==EXE_SHA
        paths=[source,H/'work/short/encoding.json',TRIMMER,Path(__file__)]
        pins = {p.relative_to(R).as_posix():sha(p) for p in paths}
        out.update(source_files_sha256=pins,solver_path=str(EXE),solver_sha256=EXE_SHA)
        observation = json.loads(subprocess.check_output(['powershell.exe','-NoProfile','-Command',
            "$o=Get-CimInstance Win32_OperatingSystem; @{free_bytes=([long]$o.FreePhysicalMemory*1024)} | ConvertTo-Json -Compress"],text=True,timeout=30))
        out['initial_resources'] = observation
        assert observation['free_bytes'] >= 1610612736, 'At least1.5GiB free physical memory is required'
        cnf,raw = W/'input.cnf',W/'raw.lrat'
        cnf.write_bytes(source.read_bytes())
        (W/'certify.exact.py').write_bytes(Path(__file__).read_bytes())
        (W/'gen_lean_core.exact.py').write_bytes(TRIMMER.read_bytes())
        nv,clauses = formula(cnf)
        out.update(variables=nv,original_clauses=len(clauses),input_sha256=sha(cnf))
        stdout,stderr = W/'stdout.txt',W/'stderr.txt'
        command = [str(EXE),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
        out.update(status='RUNNING_NATIVE_SOLVER',command=command,solver_runs=1)
        save(RECORD,out)
        begin = time.monotonic()
        with stdout.open('xb') as so,stderr.open('xb') as se:
            proc = subprocess.Popen(command,stdout=so,stderr=se,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
            out['solver_pid'] = proc.pid
            save(RECORD,out)
            try:
                code = proc.wait(timeout=60)
                out.update(exit_code=code,status='NATIVE_UNSAT_REPLAY_PENDING' if code == 20 and b's UNSATISFIABLE' in stdout.read_bytes() else 'NATIVE_NON_UNSAT')
            except subprocess.TimeoutExpired:
                out['status'] = 'TIMEOUT'
                save(RECORD,out)
                proc.kill()
                proc.wait(timeout=15)
                out['exit_code'] = proc.returncode
        out['solver_seconds'] = time.monotonic()-begin
        out.update(stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),raw_sha256=sha(raw) if raw.exists() else None,
            raw_bytes=raw.stat().st_size if raw.exists() else 0)
        save(RECORD,out)
        if out['status'] != 'NATIVE_UNSAT_REPLAY_PENDING':
            return
        sys.dont_write_bytecode = True
        spec = importlib.util.spec_from_file_location('trim132_certificate',TRIMMER)
        utility = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(utility)
        trim = W/'trimmed.lrat'
        nl,nh,ids = utility.trim_lrat(str(raw),str(trim),len(clauses))
        assert ids == sorted(set(ids)) and all(1 <= i <= len(clauses) for i in ids)
        save(W/'core-ids.json',ids)
        core = W/'core.cnf'
        core.write_bytes((f'p cnf {nv} {len(ids)}\n'+''.join(' '.join(map(str,clauses[i-1]))+' 0\n' for i in ids)).encode('ascii'))
        premises=dict(extra_cycle_cuts=[],
            interpretation='Dependencies of this trimmed proof only. Original semantic tags identify count-free bounds and the share cap; no minimality is claimed.')
        save(W/'core-premises.json',premises)
        out.update(status='TRIMMED_NATIVE_REPLAY_PENDING',trim_sha256=sha(trim),core_sha256=sha(core),
            core_ids_sha256=sha(W/'core-ids.json'),core_clauses=len(ids),lemmas=nl,hints=nh,core_premises=premises)
        save(RECORD,out)
        if nh > 2000000:
            out.update(status='NATIVE_REPLAY_PENDING_HINT_LIMIT',replay_started=False,
                replay_reason='The trimmed proof exceeds the requested2,000,000-hint limit; no replay was attempted.')
            return
        out['replay_started'] = True
        save(RECORD,out)
        replay_result = replay(trim,clauses,ids,nl,nh)
        save(W/'replay.json',replay_result)
        out.update(status='PASS_COMPLETE_NATIVE_RUP_REPLAY',replay=replay_result)
        assert all(sha(R/rel) == digest for rel,digest in pins.items())
        assert sha(EXE) == EXE_SHA
    except BaseException as error:
        out.update(status='TIMEOUT' if out['status']=='TIMEOUT' else 'FAILED',error=repr(error))
        if proc is not None and proc.poll() is None:
            proc.kill()
            proc.wait(timeout=15)
    finally:
        out.update(finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            preserved_files_sha256={p.name:sha(p) for p in W.iterdir() if p.is_file()},
            scope='One fixed native solver run on the exact prepared input. A complete independent Python RUP replay certifies the finite CNF contradiction only. Lean replay and actual-snake clause interpretation remain pending; no new global bound.')
        save(RECORD,out)
        body = '# Native count-free share13 certificate\n\nStatus: `'+out['status']+'`.\n\n'
        if 'lemmas' in out:
            body += f"The dependency-trimmed certificate has {out['lemmas']:,} deductions, {out['hints']:,} hints and {out['core_clauses']:,} original input clauses. Original clause IDs and literal occurrences are preserved.\n\n"
            body += 'This input uses only the ordinary cycle constraints from the base encoding; no added cycle exclusions.\n\n'
        if out['status'] == 'PASS_COMPLETE_NATIVE_RUP_REPLAY':
            body += 'Every trimmed deduction passed an independent ordered unit-propagation replay from the original input clauses, ending in the empty clause. The replay did not call a solver.\n\n'
        elif out['status'] == 'NATIVE_REPLAY_PENDING_HINT_LIMIT':
            body += 'The proof exceeds the requested hint limit, so complete replay remains pending.\n\n'
        elif 'error' in out:
            body += 'Failure retained: `'+out['error']+'`.\n\n'
        body += out['scope']+'\n'
        REVIEW.write_text(body,encoding='utf-8')
        print(json.dumps({k:v for k,v in out.items() if k not in ['source_files_sha256','preserved_files_sha256']},indent=2),flush=True)

if __name__ == '__main__':
    main()
