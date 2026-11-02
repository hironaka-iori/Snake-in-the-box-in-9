"""Sequential fresh checks; repeated proof trials are an explicit matched workload experiment."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PREV = HERE.parent / '90-context-witness-certificates'
GEOMETRY = HERE.parent / '89-shared-cover-certification'
BIN = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())
plans = {
    'CachePilotData': ([(HERE,'ShapeCache'),(GEOMETRY,'BalancedLookup'),(PREV,'Class001WitnessData')],0),
    'CachePilotChecks': ([(HERE,'CachePilotData'),(HERE,'ShapeCache'),(PREV,'WitnessTablesChecks'),
                         (GEOMETRY,'Balanced001Checks'),(GEOMETRY,'SharedAssembly')],5),
    'DirectPilotChecks': ([(PREV,'Class001WitnessData'),(PREV,'WitnessTablesChecks'),
                          (GEOMETRY,'Balanced001Checks'),(GEOMETRY,'SharedAssembly')],2),
}
selected = sys.argv[1:] or ['CachePilotData','DirectPilotChecks','CachePilotChecks','CachePilotChecks','DirectPilotChecks']
assert all(n in plans for n in selected)
generation = read(HERE / 'data/pilot-generation.json')
assert sha(HERE / 'scripts/build_pilot.py') == generation['script_sha256']
for name, digest in generation['input_sha256'].items():
    assert sha(ROOT / name) == digest, name
for name, digest in generation['source_sha256'].items():
    assert sha(HERE / 'lean' / name) == digest, name
support = read(PREV / 'data/WitnessLookup-audit.json')
paths = [str(HERE / 'build'),*support['paths']]
env = os.environ.copy()
env['PATH'] = str(BIN) + ';' + env['PATH']
env['LEAN_PATH'] = ';'.join(paths)
run_id = str(time.time_ns())
record_path = HERE / 'logs' / ('pilot-run-' + run_id + '.json')
record = dict(status='RUNNING',pid=os.getpid(),modules=selected,records=[],
              started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              checker_sha256=sha(Path(__file__)),
              scope='Same six class1 jobs; direct and cached proofs have the same membership conclusion. '
                    'Concurrent background loads are recorded; this is not an isolated timing experiment.')


def save():
    temporary = record_path.with_suffix('.tmp')
    temporary.write_text(json.dumps(record,indent=2)+'\n')
    os.replace(temporary,record_path)


def verify(base, module):
    rp = base / 'data' / (module + '-audit.json')
    r = read(rp)
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    for folder, ext, key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(base / folder / (module+ext)) == r[key], (module,key)
    return str(rp.relative_to(ROOT)),sha(rp)


def processes():
    command = "@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake|python)(\\.exe)?$' } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
    raw = subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
    return json.loads(raw) if raw else []


save()
try:
    for index,module in enumerate(selected):
        dependencies, expected = plans[module]
        pins = dict(verify(base,dep) for base,dep in dependencies)
        src = HERE / 'lean' / (module+'.lean')
        rp = HERE / 'data' / (module+'-audit.json')
        if module.endswith('Data') and rp.exists():
            verify(HERE,module)
            assert read(rp)['dependencies'] == pins
            record['records'].append(dict(module=module,status='REUSED_CHECKED_DATA',receipt_sha256=sha(rp)))
            save()
            continue
        log = HERE / 'logs' / (module+'.log')
        # Preserve previous compiler observations before a deliberate timing repeat.
        if log.exists():
            (HERE / 'logs' / (module+'-previous-'+sha(log)[:12]+'.log')).write_bytes(log.read_bytes())
        if rp.exists():
            (HERE / 'data' / (module+'-previous-'+sha(rp)[:12]+'.json')).write_bytes(rp.read_bytes())
        obj = HERE / 'build' / (module+'.olean')
        fresh = obj.with_name(module+'.check-'+run_id+'-'+str(index)+'.olean')
        assert not fresh.exists()
        observed = processes()
        before = sha(src)
        start = time.monotonic()
        with log.open('w',encoding='utf-8') as out:
            proc = subprocess.Popen([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),
                                     '-o',str(fresh),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,
                                    stdout=out,stderr=subprocess.STDOUT)
            record['active'] = dict(module=module,trial=index,launcher_pid=proc.pid,source_sha256=before,
                                    temporary_output=str(fresh),processes_before=observed)
            save()
            code = proc.wait()
        result = dict(module=module,trial=index,exit_code=code,seconds=time.monotonic()-start,
                      source_sha256=before,log_sha256=sha(log),dependencies=pins,
                      checker_sha256=sha(Path(__file__)),processes_before=observed)
        assert sha(src) == before, 'Source changed while compiler was active'
        trial_name = module+'-trial-'+run_id+'-'+str(index)
        (HERE/'logs'/(trial_name+'.log')).write_bytes(log.read_bytes())
        (HERE/'logs'/(trial_name+'-record.json')).write_text(json.dumps(result,indent=2)+'\n')
        (HERE/'logs'/(module+'-record.json')).write_text(json.dumps(result,indent=2)+'\n')
        if code:
            print(log.read_text()[-16000:],flush=True)
            raise RuntimeError(f'{module}: compiler exit {code}')
        output = log.read_text()
        assert 'error:' not in output and 'sorryAx' not in output
        assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
        matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
        matches += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
        assert len(matches) == expected == src.read_text().count('#print axioms')
        audits = []
        for theorem,values in matches:
            axioms = re.findall(r'[A-Za-z][\w.]*',values)
            assert set(axioms) <= {'propext','Classical.choice','Quot.sound'}
            audits.append(dict(theorem=theorem,axioms=axioms))
        os.replace(fresh,obj)
        result.update(status='PASS_REFERENCE_SHAPE_PILOT' if expected else 'PASS_REFERENCE_SHAPE_DATA',
                      olean_sha256=sha(obj),theorem_audits=audits,
                      immutable_trial_log=(HERE/'logs'/(trial_name+'.log')).relative_to(ROOT).as_posix(),
                      scope='Named concrete module only; a repeated theorem check adds no new distinct result.')
        rp.write_text(json.dumps(result,indent=2)+'\n')
        (HERE/'data'/(trial_name+'-audit.json')).write_text(json.dumps(result,indent=2)+'\n')
        record['records'].append(dict(module=module,trial=index,status=result['status'],seconds=result['seconds'],
                                      receipt_sha256=sha(rp),receipt=rp.relative_to(ROOT).as_posix(),
                                      immutable_receipt=(HERE/'data'/(trial_name+'-audit.json')).relative_to(ROOT).as_posix()))
        record.pop('active',None)
        save()
        print(module,result['status'],round(result['seconds'],3),'seconds',len(audits),'audits',flush=True)
    record['status'] = 'PASS_SELECTED_SHAPE_PILOT_TRIALS'
    record['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
except BaseException as exc:
    record['status'] = 'STOPPED_WITH_EXCEPTION'
    record['exception'] = repr(exc)
    save()
    raise
