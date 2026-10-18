"""Local live dashboard and resumable computation for the incomplete KEEP=112 proof.

Boolean certificates and solver experiments are never labelled geometric proofs.
The mathematical bridge is advanced separately by the authorized continuation task.
"""
import argparse
from datetime import datetime, timezone
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time
import traceback

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = ROOT/'outputs/lean112'
sys.path.insert(0, str(ROOT/'work'))
from build_regrowth_cnf import encode, witness_assignment

OUT.mkdir(parents=True, exist_ok=True)
EVENT_LOCK = threading.Lock()


def now():
    return datetime.now(timezone.utc).isoformat()


def read(path, default=None):
    try:
        return json.loads(path.read_text(encoding='utf-8-sig'))
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def save(name, data):
    path = OUT/name
    tmp = path.with_suffix('.tmp')
    data['updated_utc'] = now()
    with tmp.open('w', encoding='utf-8', newline='\n') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.write('\n'); f.flush(); os.fsync(f.fileno())
    for attempt in range(101):
        try:
            os.replace(tmp, path)
            return
        except PermissionError:
            if attempt == 100:
                raise
            time.sleep(.05)


def event(stage, message, **extra):
    with EVENT_LOCK:
        with (OUT/'events.jsonl').open('a', encoding='utf-8', newline='\n') as f:
            f.write(json.dumps(dict(time_utc=now(), stage=stage, message=message, **extra), ensure_ascii=False)+'\n')
            f.flush(); os.fsync(f.fileno())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def first_certificate(lean):
    folder = ROOT/'work/lean/sat-first-checked'
    modules = [folder/'Dfs112FirstBooleanInputs.lean'] + sorted(folder.glob('Dfs112FirstBooleanPart*.lean')) + [folder/'Dfs112FirstBoolean.lean']
    old = read(folder/'manifest.json', {})
    prior = read(OUT/'first-certificate.json', {})
    cache = {r['module']: r for r in old.get('checked', []) if r['exit_code'] == 0}
    cache.update({r['module']: r for r in prior.get('checked', []) if r['exit_code'] == 0})
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if 'version 4.19.0' not in version:
        raise RuntimeError(version)
    state = dict(status='RUNNING', total=len(modules), checked=[], current=None,
                 scope='Boolean clauses only; not a geometric KEEP=112 theorem.', lean_version=version)
    logdir = OUT/'first-logs'; logdir.mkdir(exist_ok=True)
    env = os.environ.copy(); env['LEAN_PATH'] = str(folder)
    reusable = True
    for path in modules:
        name = path.stem
        sha = hashlib.sha256(path.read_text(encoding='utf-8').encode()).hexdigest()
        olean = path.with_suffix('.olean')
        previous = cache.get(name, {})
        reusable = reusable and previous.get('sha256') == sha and olean.is_file()
        if reusable and previous.get('olean_sha256'):
            reusable = digest(olean) == previous['olean_sha256']
        state['current'] = name; save('first-certificate.json', state)
        if reusable:
            record = dict(module=name, sha256=sha, exit_code=0, cached=True, olean_sha256=digest(olean))
        else:
            event('certificate', f'开始检查第 {len(state["checked"])+1}/{len(modules)} 个分片', module=name)
            log = logdir/(name+'.log')
            with log.open('w', encoding='utf-8') as out:
                p = subprocess.run([str(lean), '--root='+str(folder), '-o', str(olean), str(path)],
                    cwd=folder, env=env, stdout=out, stderr=subprocess.STDOUT, timeout=900)
                out.flush(); os.fsync(out.fileno())
            text = log.read_text(encoding='utf-8')
            if p.returncode or 'sorryAx' in text or "declaration uses 'sorry'" in text:
                state.update(status='FAILED', error=f'{name}: exit={p.returncode}', log=str(log.relative_to(ROOT)))
                save('first-certificate.json', state)
                raise RuntimeError(state['error'])
            record = dict(module=name, sha256=sha, exit_code=0, cached=False, olean_sha256=digest(olean))
        state['checked'].append(record); save('first-certificate.json', state)
        if not reusable:
            event('certificate', f'分片已通过并保存：{len(state["checked"])}/{len(modules)}', module=name)
    audit = folder/'Dfs112LiveAudit.lean'
    audit.write_text('import Dfs112FirstBoolean\n#print axioms Dfs112FirstBoolean.constraints_unsat\n', encoding='utf-8')
    result = subprocess.run([str(lean), str(audit)], cwd=folder, env=env, capture_output=True, text=True, encoding='utf-8')
    (logdir/'axioms.log').write_text(result.stdout+result.stderr, encoding='utf-8')
    found = re.findall(r"'Dfs112FirstBoolean.constraints_unsat' depends on axioms: \[([^]]*)\]", result.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if result.returncode or len(found) != 1 or not set(filter(None, map(str.strip, found[0].split(',')))) <= allowed:
        raise RuntimeError('Final Boolean axiom audit failed')
    state.update(status='PASSED_BOOLEAN_ONLY', current=None, axioms=found[0], finished_utc=now())
    save('first-certificate.json', state)
    event('certificate', '首例布尔证明全部通过；仍需完成与蛇路径的数学连接。')


def survey(cadical):
    bank = [r['vertex_sequence'] for r in read(ROOT/'work/bank9.json')]
    paths = [p for s in bank for p in (s, s[::-1])]
    folder = OUT/'survey'; folder.mkdir(exist_ok=True)
    state = read(OUT/'survey.json', dict(entries={}))
    state.update(status='RUNNING', total=len(paths), current=None,
                 scope='Solver outcomes only. UNSAT is not a Lean geometric exclusion.')
    owners = {}
    for j, path in enumerate(paths):
        data = encode(path, 112, 193)
        sha = hashlib.sha256(json.dumps(data['clauses'], separators=(',', ':')).encode()).hexdigest()
        state['current'] = j; save('survey.json', state)
        prior = state['entries'].get(str(j))
        if prior and prior.get('formula_sha256') == sha and prior['status'] in ('UNSAT', 'RELAXATION_SAT'):
            owners[sha] = j
            continue
        if sha in owners:
            owner = owners[sha]
            result = dict(state['entries'][str(owner)], entry=j, reused_from=owner)
        else:
            control = encode(path, 112, len(path))
            _, failed = witness_assignment(control, path[111:])
            if failed:
                raise RuntimeError(f'Positive control rejected entry {j}: {failed[:5]}')
            prefix = folder/f'entry{j:03d}'
            prefix.with_suffix('.json').write_text(json.dumps(data, separators=(',', ':')), encoding='utf-8')
            prefix.with_suffix('.cnf').write_text(f'p cnf {data["variables"]} {len(data["clauses"])}\n'+
                ''.join(' '.join(map(str,c))+' 0\n' for c in data['clauses']), encoding='utf-8')
            start = time.monotonic()
            with prefix.with_suffix('.log').open('w', encoding='utf-8') as log:
                try:
                    p = subprocess.run([str(cadical), '--plain', '-c', '100000', '--lrat', '--no-binary',
                        str(prefix.with_suffix('.cnf')), str(prefix.with_suffix('.lrat'))],
                        stdout=log, stderr=subprocess.STDOUT, timeout=45)
                    code = p.returncode
                except subprocess.TimeoutExpired:
                    code = None
                log.flush(); os.fsync(log.fileno())
            status = 'UNSAT' if code == 20 else 'RELAXATION_SAT' if code == 10 else 'UNKNOWN'
            result = dict(entry=j, status=status, returncode=code, formula_sha256=sha,
                seconds=round(time.monotonic()-start, 2), positive_control_passed=True,
                formula=str(prefix.with_suffix('.json').relative_to(ROOT)),
                certificate=str(prefix.with_suffix('.lrat').relative_to(ROOT)) if code == 20 else None)
            owners[sha] = j
        state['entries'][str(j)] = result; save('survey.json', state)
        event('survey', f'入口 {j+1}/262 已保存：{result["status"]}', entry=j, result=result['status'])
    state.update(status='SURVEY_COMPLETE', current=None, finished_utc=now())
    save('survey.json', state)
    event('survey', '全部入口的首轮计算调查已保存；未决和可满足实例需要进一步加强方法。')


def guarded(stage, fn, *args):
    try:
        fn(*args)
    except Exception:
        detail = traceback.format_exc()
        (OUT/(stage+'-error.log')).write_text(detail, encoding='utf-8')
        name = 'first-certificate.json' if stage == 'certificate' else 'survey.json'
        state = read(OUT/name, {})
        state.update(status='FAILED', error=detail.splitlines()[-1]); save(name, state)
        event(stage, '任务遇到错误，已保存日志，等待续作修复。', error=detail.splitlines()[-1])


def snapshot():
    raw_events = (OUT/'events.jsonl').read_text(encoding='utf-8').splitlines() if (OUT/'events.jsonl').exists() else []
    events = []
    for line in raw_events[-35:]:
        try: events.append(json.loads(line))
        except json.JSONDecodeError: pass
    return dict(server_time=now(), pid=os.getpid(),
        certificate=read(OUT/'first-certificate.json', {}), survey=read(OUT/'survey.json', {}),
        reasoning=read(OUT/'reasoning.json', {}), events=events)


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path.split('?')[0] == '/api/status':
            data = json.dumps(snapshot(), ensure_ascii=False).encode('utf-8'); kind='application/json; charset=utf-8'
        elif self.path.split('?')[0] in ('/', '/index.html'):
            data = (HERE/'dashboard.html').read_bytes(); kind='text/html; charset=utf-8'
        else:
            self.send_error(404); return
        self.send_response(200)
        self.send_header('Content-Type', kind); self.send_header('Cache-Control', 'no-store')
        self.send_header('Content-Length', str(len(data))); self.end_headers(); self.wfile.write(data)
    def log_message(self, *args):
        pass


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--port', type=int, default=0)
    args=parser.parse_args()
    # Keep one server/worker set per checkout, including across independent launches.
    lock=(OUT/'service.lock').open('a+b')
    if os.name == 'nt':
        import msvcrt
        lock.seek(0); lock.write(b'0'); lock.flush(); lock.seek(0)
        msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
    server=ThreadingHTTPServer(('127.0.0.1', args.port), Handler)
    save('server.json', dict(pid=os.getpid(), url=f'http://127.0.0.1:{server.server_address[1]}', started_utc=now()))
    event('service', '后台服务已启动，进度面板可用。')
    if not (OUT/'reasoning.json').exists():
        save('reasoning.json', dict(status='PENDING', title='原路径到逻辑约束的 Lean 连接',
            detail='布尔检查与计算调查进行中；数学连接尚未完成，将由定时续作继续。',
            formally_certified_entries=0, total_entries=262))
    threading.Thread(target=guarded, args=('certificate', first_certificate, args.lean_bin/'lean.exe'), daemon=True).start()
    threading.Thread(target=guarded, args=('survey', survey, args.lean_bin/'cadical.exe'), daemon=True).start()
    server.serve_forever()


if __name__ == '__main__':
    main()
