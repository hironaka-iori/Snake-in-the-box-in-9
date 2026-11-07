"""Stream a cap-14 query from a saved cap-13 encoding, retaining path restrictions.

Remove only the old cap unit. Keep all old monotone counter implications,
add the fifteenth share bit for each of 35 occurrences, and bound their
525-bit sum by fourteen. This avoids rebuilding the base radius-four model.
"""
from pathlib import Path
import argparse
import gc
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import time
import native_resources as nr

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
OLD = R / 'milestones/180-share14-certificates'
EXE = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def private(pid):
    handle = nr.kernel.OpenProcess(0x1000, False, pid)
    if not handle:
        return 0
    try:
        value = nr.PROCESS_MEMORY_COUNTERS_EX()
        value.cb = nr.ctypes.sizeof(value)
        assert nr.psapi.GetProcessMemoryInfo(handle, nr.ctypes.byref(value), value.cb)
        return int(value.PrivateUsage)
    finally:
        nr.kernel.CloseHandle(handle)


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


parser = argparse.ArgumentParser()
parser.add_argument('shape', choices=['012034', '012301', '012340', '012345'])
args = parser.parse_args()
label = args.shape + '-floor15'
record_path = H / 'data' / (label + '.json')
assert not record_path.exists(), 'Preserve previous attempts and inspect their terminal state.'
initial = nr.snapshot()
record = {'shape': args.shape, 'status': 'PREPARING', 'target_share': 15,
          'cap': 14, 'producer_sha256': sha(__file__), 'initial_resources': initial}
if initial['errors'] or initial['processes'] or initial['free_bytes'] < 1024**3:
    record['status'] = 'NOT_STARTED_RESOURCE_GATE'
    save(record_path, record)
    print(record['status'], flush=True)
    raise SystemExit(0)
assert sha(EXE) == '4fb5f4f94a3632c185ea763f7da627d40038cca38d9481952d00d04cc881c94f'
native = json.loads((OLD / 'data' / (args.shape + '.json')).read_text())
source = OLD / 'certificates' / (args.shape + '.cnf.gz')
semantic = OLD / 'certificates' / (args.shape + '.meanings.json.gz')
assert sha(source) == native['artifacts'][source.name]
assert sha(semantic) == native['artifacts'][semantic.name]
meaning = json.loads(gzip.decompress(semantic.read_bytes()))
tots = meaning['tots']
assert len(tots) == 71 and len(tots[-1][0]) == 490
assert meaning['tags'][-1] == ['shareCap', 70]
roots = {tuple(v): int(k) for k, v in meaning['smeaning'].items() if v[0] == 't'}
primary = {int(v[1]): int(k) for k, v in meaning['meaning'].items() if v[0] == 'p'}
old_cap = roots[('t', 70, 0, 490, 14)]
nv = native['variables']
cache = H / 'cache' / label
cache.mkdir(parents=True)
tail_path = cache / 'added.cnf'
added = 0
new_meanings = {}
share_bits = list(tots[-1][0])


def fresh(value):
    global nv
    nv += 1
    new_meanings[nv] = value
    return nv


with tail_path.open('w', encoding='ascii', newline='\n') as tail:
    def add(clause):
        global added
        tail.write(' '.join(map(str, clause)) + ' 0\n')
        added += 1

    for index in range(35):
        et, dt = 2 * index, 2 * index + 1
        assert len(tots[et][0]) == 28 and len(tots[dt][0]) == 9
        q = tots[et][1][1]
        assert tots[et][1] == ['emp', q] and tots[dt][1] == ['nb', q]
        old_bits = tots[-1][0][14 * index:14 * (index + 1)]
        assert all(meaning['smeaning'][str(v)] == ['u', q, t]
                   for t, v in enumerate(old_bits, 1))
        u = fresh(['u', q, 15, index])
        share_bits.append(u)
        for d in range(1, 10):
            need = (15 * d + 11) // 12
            clause = [u, -roots[('t', et, 0, 28, need)]]
            if d < 9:
                clause.append(roots[('t', dt, 0, 9, d + 1)])
            add(clause)

    def counter(lo, hi):
        if hi - lo == 1:
            return [None, share_bits[lo]]
        mid = (lo + hi) // 2
        a, b = counter(lo, mid), counter(mid, hi)
        out = [None] + [fresh(['cap15', lo, hi, t]) for t in range(1, min(hi - lo, 15) + 1)]
        for i in range(len(a)):
            for j in range(len(b)):
                if 0 < i + j < len(out):
                    add([out[i + j]] + ([-a[i]] if i else []) + ([-b[j]] if j else []))
        return out

    out = counter(0, len(share_bits))
    add([-out[15]])
    path_clauses = []
    if args.shape == '012301':
        path_clauses = [[-primary[4]], [-primary[8]]]
        extension = sorted(({1 << a for a in range(9)} - {1}) |
                           ({12 ^ (1 << a) for a in range(9)} - {14}))
        path_clauses.append([primary[q] for q in extension])
        for clause in path_clauses:
            add(clause)

cnf = cache / 'input.cnf'
digest = hashlib.sha256()
with gzip.open(source, 'rb') as src, cnf.open('wb') as dst:
    header = src.readline()
    digest.update(header)
    _, _, old_nv, old_nc = header.split()
    old_nv, old_nc = int(old_nv), int(old_nc)
    assert old_nv == native['variables'] and old_nc == native['clauses']
    dst.write(f'p cnf {nv} {old_nc - 1 + added}\n'.encode())
    for index, line in enumerate(src, 1):
        digest.update(line)
        if index < old_nc:
            dst.write(line)
        else:
            assert index == old_nc and list(map(int, line.split())) == [-old_cap, 0]
    assert index == old_nc and digest.hexdigest() == native['cnf_sha256']
    with tail_path.open('rb') as extra:
        shutil.copyfileobj(extra, dst)
with cnf.open('rb') as src, gzip.open(H / 'certificates' / (label + '.cnf.gz'), 'wb') as dst:
    shutil.copyfileobj(src, dst)
delta = {'source_semantics_sha256': sha(semantic), 'removed_cap_unit': [-old_cap],
         'new_meanings': new_meanings, 'new_cap_bits': share_bits, 'new_cap_output': out[15],
         'path_clauses': path_clauses}
with gzip.open(H / 'certificates' / (label + '.delta.json.gz'), 'wt') as dst:
    json.dump(delta, dst)
record.update(status='RUNNING', source_cnf_sha256=digest.hexdigest(), source_semantics_sha256=sha(semantic),
              cnf_sha256=sha(cnf), variables=nv, clauses=old_nc-1+added,
              removed_clause=[-old_cap], added_clauses=added, path_clauses=path_clauses,
              private_limit=256*1024**2, reserve=768*1024**2,
              peak_private=private(os.getpid()), solver_sha256=sha(EXE))
del meaning, roots, tots, new_meanings
gc.collect()
raw = cache / 'raw.lrat'
stdout, stderr = H / 'logs' / (label + '.stdout'), H / 'logs' / (label + '.stderr')
command = [str(EXE), '-q', '--lrat', '--no-binary', '--seed=1', str(cnf), str(raw)]
start = time.monotonic()
with stdout.open('wb') as so, stderr.open('wb') as se:
    child = subprocess.Popen(command, stdout=so, stderr=se,
                             creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
    record.update(pid=child.pid, command=command)
    save(record_path, record)
    try:
        while child.poll() is None:
            snapshot = nr.snapshot()
            owned = private(os.getpid()) + private(child.pid)
            record['peak_private'] = max(record['peak_private'], owned)
            if snapshot['errors'] or snapshot['processes'] or snapshot['free_bytes'] < 768*1024**2 or owned > 256*1024**2:
                record.update(status='RESOURCE_STOP', stop_snapshot=snapshot)
                child.terminate()
                break
            if time.monotonic() - start > 90 or (raw.exists() and raw.stat().st_size > 128*1024**2):
                record['status'] = 'BOUNDED_STOP'
                child.terminate()
                break
            time.sleep(.25)
        code = child.wait(timeout=15)
    finally:
        if child.poll() is None:
            child.terminate()
            child.wait(timeout=15)
record.update(exit_code=code, seconds=time.monotonic()-start,
              raw_sha256=sha(raw) if raw.exists() else None,
              raw_bytes=raw.stat().st_size if raw.exists() else 0)
if record['status'] == 'RUNNING':
    record['status'] = ('UNSAT_NATIVE_REPLAY_PENDING' if code == 20 and b's UNSATISFIABLE' in stdout.read_bytes()
                        else 'SAT_NATIVE' if code == 10 else 'UNRESOLVED')
if raw.exists():
    with raw.open('rb') as src, gzip.open(H / 'certificates' / (label + '.lrat.gz'), 'wb') as dst:
        shutil.copyfileobj(src, dst)
record['artifacts'] = {p.name: sha(p) for p in (H / 'certificates').glob(label + '.*')}
save(record_path, record)
print(args.shape, record['status'], round(record['seconds'], 2), record['raw_bytes'], flush=True)
