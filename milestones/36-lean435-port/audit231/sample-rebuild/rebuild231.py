#!/usr/bin/env python3
"""Sampling rebuild of the 231 certificates (evidence that the farm's single kernel checks reproduce).

    rebuild231.py sample [--seed S] [--out sample.jsonl]     seeded sample, stratified by replay hints
    rebuild231.py run [--list sample.jsonl] [--out results.jsonl] [--jobs 3] [--hours H]
    rebuild231.py summary [--out results.jsonl]

The population is the 24,797 lines of ../manifest231.jsonl.gz (the certificates the 231 glue imports).
Strata: the 10 equal-count deciles of `hints`; the five split certificates (SPLIT.md, kernel checks in part
modules) are excluded, and in the top decile only items of at most --max-hints (default 20 M) are drawn, so
one build stays under ~3 h. The per-stratum counts are in COUNTS. Drawing: random.Random(seed).sample of
each stratum, in manifest order sorted by module name.

Each item is rebuilt from its plan (certplan231_* in milestones/28-combined-identities/data, freeplan_* and
freeseeds_* in lean435/data) by `prod435.py one`: the same generators (cert231 through cert435, CaDiCaL
2.1.3, gen_lean_lrat_v3, to435), the same core stack (core manifest sha256 checked) and Lean 4.35.0, with the
kernel check of the build. Compared with the manifest line: the sha256 of the regenerated source and of the
public `.olean` (the file the 231 audit consumed), plus the other parts for information.
"""
import argparse, gzip, json, os, random, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
MAN = os.path.join(HERE, '..', 'manifest231.jsonl.gz')
PROD = os.path.join(ROOT, 'lean435', 'tools', 'prod435.py')
HOME = os.environ.get('PROD435_HOME', os.path.expanduser('~/l435/prod'))
JOBS = os.path.join(HOME, 'jobs-audit231')
COUNTS = [30, 30, 30, 30, 30, 30, 30, 30, 25, 10]
SPLIT = {'T012301A36264K45', 'T012301A46246K33', 'T012301A33436K47', 'T012301A35353K20', 'T012301A26346K35'}


def plan_path(name):
    for d in (os.path.join(ROOT, 'milestones', '28-combined-identities', 'data'), os.path.join(ROOT, 'lean435', 'data')):
        if os.path.exists(os.path.join(d, name)):
            return os.path.join(d, name)
    raise SystemExit(f'plan {name} not found')


def seeds_path(plan):
    if plan.startswith('freeplan_'):
        p = os.path.join(ROOT, 'lean435', 'data', plan.replace('freeplan_', 'freeseeds_'))
        return p if os.path.exists(p) else None
    return None


def load():
    return [json.loads(l) for l in gzip.open(MAN, 'rt')]


def cmd_sample(a):
    R = sorted(load(), key=lambda r: ((r['hints'] or 0), r['module']))
    n = len(R)
    out = []
    for d, k in enumerate(COUNTS):
        X = [r for r in R[d * n // 10:(d + 1) * n // 10] if r['name'] not in SPLIT and (r['hints'] or 0) <= a.max_hints]
        X.sort(key=lambda r: r['module'])
        for r in random.Random(f'{a.seed}-{d}').sample(X, k):
            out.append(dict(stratum=d, module=r['module'], name=r['name'], plan=r['plan'], kind=r['kind'],
                            hints=r['hints'], lean_cpu_s=r['lean_cpu_s'], generator_commit=r['generator_commit'],
                            source_sha256=r['source_sha256'], olean_sha256=r['parts']['.olean'], parts=r['parts']))
    with open(a.out, 'w') as f:
        f.write(json.dumps(dict(seed=a.seed, max_hints=a.max_hints, counts=COUNTS, population=n,
                                manifest_sha256_gz=subprocess.run(['sha256sum', MAN], capture_output=True,
                                                                  text=True).stdout.split()[0])) + '\n')
        for x in out:
            f.write(json.dumps(x) + '\n')
    print(f'{len(out)} items -> {a.out}')


def cmd_run(a):
    lines = [json.loads(l) for l in open(a.list)]
    items = lines[1:]
    done = set()
    if os.path.exists(a.out):
        done = {json.loads(l)['module'] for l in open(a.out) if l.strip()}
    todo = [it for it in items if it['module'] not in done]
    todo.sort(key=lambda it: (it['hints'] or 0) * (1 if a.smallest_first else -1))   # default: largest first
    if a.strata:
        todo = [it for it in todo if it['stratum'] in a.strata]
    if a.only:
        todo = [it for it in todo if it['name'] in a.only]
    lock = threading.Lock()
    t_end = time.time() + a.hours * 3600
    env = {k: v for k, v in os.environ.items() if k not in ('PROD435_ADAPTER', 'PROD435_CERT', 'C230_PLAN')}
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    # prod435's per-plan self-seed file, written once here (concurrent `one` jobs would race on its .tmp)
    for k in ('PROD435_ADAPTER', 'PROD435_CERT', 'C230_PLAN'):
        os.environ.pop(k, None)
    import importlib.util
    spec = importlib.util.spec_from_file_location('prod435', PROD)
    P = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(P)
    for pl in sorted({it['plan'] for it in todo if not seeds_path(it['plan'])}):
        P.seeds_file(plan_path(pl))
    core_sha = subprocess.run(['sha256sum', os.path.join(HOME, 'core', 'core-manifest.jsonl')], capture_output=True,
                              text=True).stdout.split()[0]

    def work():
        while True:
            with lock:
                if not todo or time.time() > t_end or os.path.exists(os.path.join(HERE, 'STOP')):
                    return
                it = todo.pop(0)
                if os.path.exists(a.out) and any(json.loads(l)['module'] == it['module'] for l in open(a.out) if l.strip()):
                    continue                                      # done meanwhile by another run process
            D = os.path.join(JOBS, it['name'])
            os.makedirs(D, exist_ok=True)
            if os.path.exists(os.path.join(D, 'result.json')):
                os.remove(os.path.join(D, 'result.json'))
            plan = plan_path(it['plan'])
            cmd = [sys.executable, PROD, 'one', '--plan', plan, '--name', it['name'], '--job-dir', D, '--mem-gb', str(a.mem_gb)]
            sp = seeds_path(it['plan'])
            if sp:
                cmd += ['--seeds', sp]
            t0 = time.time()
            r = subprocess.run(cmd, env=env, capture_output=True, text=True)
            wall = round(time.time() - t0, 1)
            try:
                res = json.load(open(os.path.join(D, 'result.json')))
            except (OSError, ValueError):
                res = dict(error=f'no result (exit {r.returncode}): {(r.stdout + r.stderr)[-600:]}')
            row = dict(stratum=it['stratum'], module=it['module'], kind=it['kind'], plan=it['plan'], hints=it['hints'],
                       farm_generator_commit=it['generator_commit'], rebuild_commit=head, rebuild_core_manifest=core_sha,
                       wall_s=wall)
            if 'error' in res:
                row.update(result='ERROR', error=res['error'][-600:])
            else:
                src_ok = res['source_sha256'] == it['source_sha256']
                ol_ok = res['parts'].get('.olean') == it['olean_sha256']
                row.update(result='MATCH' if ol_ok else 'MISMATCH', olean_sha256=res['parts'].get('.olean'),
                           manifest_olean_sha256=it['olean_sha256'], source_match=src_ok,
                           source_sha256=res['source_sha256'], rebuilt_hints=res['hints'],
                           other_parts_match={e: res['parts'].get(e) == it['parts'].get(e)
                                              for e in it['parts'] if e != '.olean'},
                           lean_cpu_s=res['lean_cpu_s'], farm_lean_cpu_s=it['lean_cpu_s'], peak_anon_gb=res['peak_anon_gb'],
                           kernel_checked=True, lean=res['lean'], host=res['host'], t=res['t'])
                if not a.keep:
                    subprocess.run(['rm', '-rf', D])
            with lock:
                with open(a.out, 'a') as f:
                    f.write(json.dumps(row, sort_keys=True) + '\n')
                print(time.strftime('%H:%M:%S'), row['result'], it['module'], it['hints'], f'{wall:.0f} s',
                      '' if row.get('source_match', True) else 'SOURCE DIFFERS', flush=True)

    ths = [threading.Thread(target=work) for _ in range(a.jobs)]
    for t in ths:
        t.start()
    for t in ths:
        t.join()


def cmd_summary(a):
    rows, seen, dup = [], set(), 0
    for l in open(a.out):
        if l.strip():
            r = json.loads(l)
            if r['module'] in seen:                       # rebuilt twice by two run processes: the first row counts
                dup += 1
                continue
            seen.add(r['module'])
            rows.append(r)
    by = {}
    for r in rows:
        by.setdefault(r['stratum'], []).append(r)
    tot = {}
    for r in rows:
        tot[r['result']] = tot.get(r['result'], 0) + 1
    print(json.dumps(dict(total=len(rows), duplicates=dup, results=tot,
                          source_match=sum(1 for r in rows if r.get('source_match')),
                          hints=sum(r['hints'] or 0 for r in rows),
                          lean_cpu_h=round(sum(r.get('lean_cpu_s') or 0 for r in rows) / 3600, 2))))
    for d in sorted(by):
        X = by[d]
        print(d, len(X), {k: sum(1 for r in X if r['result'] == k) for k in ('MATCH', 'MISMATCH', 'ERROR')},
              min(r['hints'] for r in X), max(r['hints'] for r in X))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['sample', 'run', 'summary'])
    ap.add_argument('--seed', default='231-sample-20261118')
    ap.add_argument('--max-hints', type=float, default=20e6)
    ap.add_argument('--list', default=os.path.join(HERE, 'sample.jsonl'))
    ap.add_argument('--out', default=None)
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--hours', type=float, default=10)
    ap.add_argument('--only', nargs='*')
    ap.add_argument('--keep', action='store_true')
    ap.add_argument('--smallest-first', action='store_true')
    ap.add_argument('--mem-gb', type=float, default=12, help='memory budget of the builds (prod435 one --mem-gb)')
    ap.add_argument('--strata', type=int, nargs='*', help='only these strata (a second run process beside a first one)')
    a = ap.parse_args()
    if a.out is None:
        a.out = os.path.join(HERE, 'sample.jsonl' if a.cmd == 'sample' else 'results.jsonl')
    {'sample': cmd_sample, 'run': cmd_run, 'summary': cmd_summary}[a.cmd](a)
