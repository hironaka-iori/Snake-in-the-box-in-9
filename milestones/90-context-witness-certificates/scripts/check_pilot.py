"""Sequential checks of the balanced witness tables and six-direction pilot."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PREV = HERE.parent / '89-shared-cover-certification'
OLD = HERE.parent / '88-retention-diagram-certificate'
BIN = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())
plans = {
    'WitnessTablesData': ([(PREV,'BalancedLookup'),(OLD,'BoxWitness')], 0),
    'WitnessTablesChecks': ([(HERE,'WitnessTablesData'),(HERE,'WitnessLookup')], 8),
    'Class001WitnessData': ([(OLD,'BoxWitness')], 0),
    'Class001WitnessChecks': ([(HERE,'Class001WitnessData'),(HERE,'WitnessTablesChecks'),
                              (PREV,'Balanced001Checks'),(PREV,'SharedAssembly')], 2),
}
selected = sys.argv[1:] or list(plans)
assert all(n in plans for n in selected)
for name, script in [('witness-table-generation.json','build_witness_tables.py'),
                     ('class001-generation.json','build_class001.py')]:
    generation = read(HERE / 'data' / name)
    assert sha(HERE / 'scripts' / script) == generation['script_sha256']
    for path, digest in generation['input_sha256'].items():
        assert sha(ROOT / path) == digest
    for filename, digest in generation['source_sha256'].items():
        assert sha(HERE / 'lean' / filename) == digest
support = read(HERE / 'data/WitnessLookup-audit.json')
paths = support['paths']
env = os.environ.copy()
env['PATH'] = str(BIN) + ';' + env['PATH']
env['LEAN_PATH'] = ';'.join(paths)
run_id = str(time.time_ns())
record_path = HERE / 'logs' / ('pilot-run-' + run_id + '.json')
record = dict(status='RUNNING', pid=os.getpid(), modules=selected, records=[],
              started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              checker_sha256=sha(Path(__file__)),
              scope='Concrete witness tables and class1 numeric membership. No full 791-context theorem or new bound.')


def save():
    temporary = record_path.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    os.replace(temporary, record_path)


def verify(base, module):
    rp = base / 'data' / (module + '-audit.json')
    r = read(rp)
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    for folder, ext, key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(base / folder / (module + ext)) == r[key], (module, key)
    return str(rp.relative_to(ROOT)), sha(rp)


save()
try:
    for module in selected:
        dependencies, expected = plans[module]
        pins = dict(verify(base, dep) for base, dep in dependencies)
        src = HERE / 'lean' / (module + '.lean')
        rp = HERE / 'data' / (module + '-audit.json')
        if rp.exists():
            verify(HERE, module)
            assert read(rp)['dependencies'] == pins
            record['records'].append(dict(module=module, status='REUSED_CHECKED_MODULE', receipt_sha256=sha(rp)))
            save()
            print(module, 'REUSED', flush=True)
            continue
        log = HERE / 'logs' / (module + '.log')
        if log.exists():
            (HERE / 'logs' / (module + '-previous-' + sha(log)[:12] + '.log')).write_bytes(log.read_bytes())
        obj = HERE / 'build' / (module + '.olean')
        fresh = obj.with_name(module + '.check-' + run_id + '.olean')
        assert not fresh.exists()
        start = time.monotonic()
        with log.open('w',encoding='utf-8') as out:
            proc = subprocess.Popen([str(BIN / 'lake.exe'),'env','lean','-s','65536','-R',str(HERE / 'lean'),
                                     '-o',str(fresh),str(src)],cwd=BIN.parent.parent / 'mathlib',env=env,
                                    stdout=out,stderr=subprocess.STDOUT)
            record['active'] = dict(module=module, launcher_pid=proc.pid, source_sha256=sha(src), temporary_output=str(fresh))
            save()
            code = proc.wait()
        result = dict(module=module, exit_code=code, seconds=time.monotonic()-start, source_sha256=sha(src),
                      log_sha256=sha(log), dependencies=pins, checker_sha256=sha(Path(__file__)))
        (HERE / 'logs' / (module + '-record.json')).write_text(json.dumps(result,indent=2)+'\n')
        if code:
            print(log.read_text()[-18000:],flush=True)
            raise RuntimeError(f'{module}: compiler exit {code}')
        text = log.read_text()
        assert 'error:' not in text and 'sorryAx' not in text
        assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
        audits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
        assert len(audits) == expected == src.read_text().count('#print axioms')
        checked = []
        for theorem, axioms in audits:
            values = re.findall(r'[A-Za-z][\w.]*',axioms)
            assert set(values) <= {'propext','Classical.choice','Quot.sound'}
            checked.append(dict(theorem=theorem,axioms=values))
        os.replace(fresh,obj)
        result.update(status='PASS_CONCRETE_WITNESS_PROOFS' if expected else 'PASS_CONCRETE_WITNESS_DATA',
                      olean_sha256=sha(obj),theorem_audits=checked,
                      scope='The named table or class1 proof module only. Full witness coverage and graph interpretation remain separate.')
        rp.write_text(json.dumps(result,indent=2)+'\n')
        record['records'].append(dict(module=module,status=result['status'],receipt_sha256=sha(rp)))
        record.pop('active',None)
        save()
        print(module,result['status'],round(result['seconds'],3),'seconds',len(checked),'audits',flush=True)
    record['status'] = 'PASS_SELECTED_WITNESS_PILOT_MODULES'
    record['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
except BaseException as exc:
    record['status'] = 'STOPPED_WITH_EXCEPTION'
    record['exception'] = repr(exc)
    save()
    raise
