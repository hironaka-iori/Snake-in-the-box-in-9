"""Prepare the bounded Lean replay without compiling or changing accepted evidence."""
from pathlib import Path
import hashlib
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R / 'milestones/160-share18-replay-transport'

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def read(p):
    return json.loads(Path(p).read_text(encoding='utf-8-sig'))

def write(p, content):
    b = content.encode('utf-8') if isinstance(content, str) else content
    p.parent.mkdir(parents=True, exist_ok=True)
    if p.exists():
        assert p.read_bytes() == b, str(p)
    else:
        p.write_bytes(b)

def main():
    sp = H / 'data/full-source-plan.json'
    source = read(sp)
    assert source['status'] == 'SOURCE_PREPARED_UNCHECKED'
    pins = {}

    def pin(path, expected=None):
        p = Path(path)
        if not p.is_absolute():
            p = R / p
        d = sha(p)
        assert expected is None or d == expected, str(p)
        pins[str(p)] = d

    pin(sp)
    for p, d in source['input_pins'].items():
        pin(p, d)
    pin(H / 'data/preparation.json', source['preparation_sha256'])
    pin(H / source['source_size_measurement'], source['source_size_measurement_sha256'])
    old_plan = P / 'data/checkpoint-execution.json'
    previous = read(old_plan)
    pin(old_plan)
    for p, d in previous['input_pins'].items():
        pin(p, d)
    completion = P / 'data/completion.json'
    assert read(completion)['status'] == 'PASS_ACCEPTED_PREFIX_CHECKPOINT_TRUTH'
    pin(completion)
    for module in previous['new_module_order']:
        rp = P / 'data' / (module + '-audit.json')
        q = read(rp)
        assert q['status'] == 'PASS' and q['exit_code'] == 0 and q['stop_reason'] is None
        pin(rp)
        for key, digest in [('source', 'source_sha256'), ('object', 'olean_sha256'), ('log', 'log_sha256')]:
            pin(q[key], q[digest])
        for path, digest in q['dependencies'].items():
            pin(path, digest)
    source_sha = {}
    for item in source['artifacts']:
        p = H / item['path']
        assert p == H / 'lean' / (item['module'].replace('.', '/') + '.lean')
        assert sha(p) == item['sha256'] and p.stat().st_size == item['bytes']
        source_sha[item['module']] = item['sha256']
    order = source['module_order']
    pilot = source['pilot_module_order']
    assert len(order) == len(set(order)) == len(source_sha)
    assert set(order) == set(source_sha) and set(pilot) <= set(order)
    transport = Path(source['transport_receipt'])
    if not transport.is_absolute():
        transport = H / transport
    pin(transport, source['transport_receipt_sha256'])
    assert read(transport)['status'] == 'PASS_COMPLETE_REMAINING_TRANSPORT_ONLY'
    run_status = transport.parent / 'run-status.json'
    assert read(run_status)['status'] == 'PASS_REMAINING_TRANSPORT_AND_UNCHECKED_SOURCES'
    pin(run_status)

    checker = (P / 'scripts/check_checkpoint.py').read_text(encoding='utf-8')
    checker = checker.replace('Check one unchanged144 semantic module using accepted generic foundations.',
                              'Check one continuation module using the accepted prefix checkpoint.')
    checker = checker.replace('data/checkpoint-execution.json', 'data/kernel-execution.json')
    checker = checker.replace("def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))", """def retry(action):
    for attempt in range(40):
        try:return action()
        except PermissionError:
            if attempt==39:raise
            time.sleep(.05)
def read(p):return retry(lambda:json.loads(Path(p).read_text(encoding='utf-8-sig')))""")
    checker = checker.replace("def save(p,j):p.write_text(json.dumps(j,indent=2)+'\\n',encoding='utf-8')", """def save(p,j):
    tmp=p.with_name(p.name+'.'+str(os.getpid())+'.tmp')
    retry(lambda:tmp.write_text(json.dumps(j,indent=2)+'\\n',encoding='utf-8'))
    retry(lambda:os.replace(tmp,p))""")
    # Preserve the successful module checker and its resource limits. No worker runs here.
    write(H / 'scripts/check_replay.py', checker)
    write(H / 'scripts/native_resources.py', (P / 'scripts/native_resources.py').read_bytes())
    for name in ['check_replay.py', 'native_resources.py', 'run_replay.py', 'prepare_kernel_execution.py']:
        pin(H / 'scripts' / name)
    search = [str(H / 'build')] + previous['search_paths']
    plan = dict(status='PREPARED_KERNEL_REPLAY_PENDING', module_order=order,
                new_module_order=order, pilot_module_order=pilot, source_sha256=source_sha,
                input_pins=pins, lean_bin=previous['lean_bin'], search_paths=search,
                checker_sha256=sha(H / 'scripts/check_replay.py'),
                driver_sha256=sha(H / 'scripts/run_replay.py'),
                scope='Remaining144160 deductions after the accepted1055-deduction checkpoint; no actual-snake bridge or global bound.')
    write(H / 'data/kernel-execution.json', json.dumps(plan, indent=2) + '\n')
    print('PREPARED_KERNEL_REPLAY', len(order), 'PILOT', len(pilot))

if __name__ == '__main__':
    main()
