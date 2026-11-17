#!/usr/bin/env python3
"""Build a split certificate (split435.py) on several machines and publish it like prod435.py.

    splitfarm435.py pack  --src SRC --name N                 push the split sources to xfer/c435split/src-N
    splitfarm435.py part  --name N --k K [--k K2 ...] [--rss-gb 14]   (part machine) fetch the sources, check
                          their sha256, build Cnf, D*, Ps and the parts K, push them to xfer/c435split/N-k<K>
    splitfarm435.py final --name N --plan P --index J        fetch every part, check that each was built on the
                          same Cnf/D/Ps .olean (sha256) as here, build the final module, write the record
                          and publish it to xfer/c435help/w<J> (prod435 helper family, claim h<J>)
    splitfarm435.py status --name N                          which parts are published

Work directory: $PROD435_HOME/split/N (default ~/l435/prod/split/N). The core stack must have been built
(`prod435.py setup`). Sources travel gzip-compressed, one blob per module; SPLIT-MANIFEST.N.json (written by
split435.py) holds the sha256 of every source and is checked on every machine. A part branch holds
<Module>{.olean,.olean.server,.olean.private,.ir,.ir.sig,.stamp} of its K modules (a few hundred KB) and
manifest.jsonl (audit.py manifest lines of the Cnf, D*, Ps and K modules it built).

Soundness: a K part's .olean is a kernel-checked statement `ok<c> : check ... Ps t<c> c = true` about the
constants of Cnf/D/Ps. The final machine accepts a part only if every one of those modules has, in that
part's manifest, the same source sha256 AND the same .olean sha256 as the final machine's own build, so the
names refer to the same definitions. The final module is then type-checked against them by lean as usual.
"""
import argparse, gzip, json, os, shutil, socket, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import prod435 as P  # noqa: E402

SPFX = 'refs/heads/xfer/c435split/'
PARTS = P.PARTS + ('.stamp',)


def wd(name):
    return os.path.join(P.HOME, 'split', name)


def rel(m):
    return m.replace('.', '/')


def manifest_of(name, src):
    return json.load(open(os.path.join(src, f'SPLIT-MANIFEST.{name}.json')))


def cmd_pack(a):
    src = os.path.abspath(a.src)
    man = manifest_of(a.name, src)
    add = {f'SPLIT-MANIFEST.{a.name}.json': open(os.path.join(src, f'SPLIT-MANIFEST.{a.name}.json'), 'rb').read()}
    for m, h in man['sources'].items():
        p = os.path.join(src, rel(m) + '.lean')
        assert P.sha(p) == h, f'{m}: source differs from the split manifest'
        add[m + '.lean.gz'] = gzip.compress(open(p, 'rb').read(), compresslevel=6, mtime=0)
        assert len(add[m + '.lean.gz']) < 95e6, f'{m}: blob above the 100 MB file limit'
    repo = P.Repo(SPFX)
    tips = repo.ls()
    ref = f'src-{a.name}'
    if ref in tips:
        raise SystemExit(f'{SPFX}{ref} exists already ({tips[ref][:10]})')
    c = repo.push(ref, add, None, f'split435 sources of {a.name}: {len(man["sources"])} modules')
    print(f'pushed {len(add)} files ({sum(len(v) for v in add.values()) / 1e6:.1f} MB) -> {SPFX}{ref} {c[:10]}')


def fetch_src(name):
    """The split sources in wd(name)/src, checked against the manifest; returns the manifest."""
    src = os.path.join(wd(name), 'src')
    mp = os.path.join(src, f'SPLIT-MANIFEST.{name}.json')
    if os.path.exists(mp):
        man = json.load(open(mp))
        if all(os.path.exists(os.path.join(src, rel(m) + '.lean')) and P.sha(os.path.join(src, rel(m) + '.lean')) == h
               for m, h in man['sources'].items()):
            return man
    repo = P.Repo(SPFX)
    t0 = time.time()
    repo.fetch([f'src-{name}'])
    ent = repo.entries(f'src-{name}')
    os.makedirs(src, exist_ok=True)
    blob = lambda path: P.git('cat-file', 'blob', ent[path], cwd=repo.b, binary=True)  # noqa: E731
    man = json.loads(blob(f'SPLIT-MANIFEST.{name}.json'))
    for m, h in man['sources'].items():
        p = os.path.join(src, rel(m) + '.lean')
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'wb').write(gzip.decompress(blob(m + '.lean.gz')))
        if P.sha(p) != h:
            raise SystemExit(f'{m}: fetched source sha256 differs from the split manifest')
    open(mp, 'w').write(json.dumps(man, indent=1))
    P.log(f'split sources of {name}: {len(man["sources"])} modules fetched and checked in {time.time() - t0:.0f} s')
    return man


def base_modules(man):
    pre = f'LocalWindowCertSplit.{man["name"]}'
    return [f'{pre}.Cnf'] + [d[0] for d in man['data']] + [f'{pre}.Ps']


def build(src, bld, targets, rss_gb, jobs, big=()):
    cmd = [sys.executable, os.path.join(HERE, 'build.py'), '--src', src, '--build', bld, '--lib', P.CORE,
           '--jobs', str(jobs), '--rss-gb', str(rss_gb)] + [x for m in big for x in ('--big', f'{m}={rss_gb}')] + targets
    r = subprocess.run(cmd)
    if r.returncode != 0:
        raise SystemExit(f'build failed: {targets}')


def audit_manifest(src, bld, mods):
    out = os.path.join(bld, 'split-manifest.jsonl')
    if os.path.exists(out):
        os.remove(out)
    subprocess.run([sys.executable, os.path.join(HERE, 'audit.py'), 'manifest', '--src', src, '--build', bld,
                    '--out', out] + mods, check=True, capture_output=True)
    return [json.loads(l) for l in open(out) if l.strip()]


def cmd_part(a):
    man = fetch_src(a.name)
    src, bld = os.path.join(wd(a.name), 'src'), os.path.join(wd(a.name), 'build')
    names = {int(p[0].rsplit('.K', 1)[1]): p[0] for p in man['parts']}
    ks = [names[k] for k in a.k]
    base = base_modules(man)
    t0 = time.time()
    build(src, bld, base, 6.0, a.jobs)
    P.log(f'{a.name}: base modules (Cnf, {len(man["data"])} data, Ps) built in {time.time() - t0:.0f} s')
    t1 = time.time()
    build(src, bld, ks, a.rss_gb, len(ks))         # the parts of this machine in parallel, each under --rss-gb
    P.log(f'{a.name}: {ks} built in {time.time() - t1:.0f} s')
    for m in ks:
        lines = audit_manifest(src, bld, base + [m])
        log = [json.loads(l) for l in open(os.path.join(bld, 'build-log.jsonl')) if l.strip()]
        add = {'manifest.jsonl': ('\n'.join(json.dumps(r, sort_keys=True) for r in lines) + '\n').encode(),
               'build-log.jsonl': ('\n'.join(json.dumps(r) for r in log if r['module'] == m) + '\n').encode(),
               'record.json': json.dumps(dict(name=a.name, module=m, host=socket.gethostname(),
                                              generator_commit=P.git('rev-parse', 'HEAD', cwd=ROOT).strip(),
                                              t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))).encode()}
        for e in PARTS:
            add[m + e] = open(os.path.join(bld, rel(m) + e), 'rb').read()
        repo = P.Repo(SPFX)
        ref = f'{a.name}-k{m.rsplit(".K", 1)[1]}'
        tip = repo.ls().get(ref)
        if tip:
            repo.fetch([ref])
        c = repo.push(ref, add, tip, f'split435 part {m}')
        P.log(f'published {m} -> {SPFX}{ref} {c[:10]}')


def cmd_status(a):
    tips = P.Repo(SPFX).ls()
    for k in sorted(tips):
        if k.startswith(a.name) or k == f'src-{a.name}':
            print(k, tips[k][:10])


def cmd_final(a):
    man = fetch_src(a.name)
    src, bld = os.path.join(wd(a.name), 'src'), os.path.join(wd(a.name), 'build')
    base = base_modules(man)
    build(src, bld, base, 6.0, a.jobs)
    mine = {r['module']: r for r in audit_manifest(src, bld, base)}
    repo = P.Repo(SPFX)
    tips = repo.ls()
    kmods = [p[0] for p in man['parts']]
    got, rlogs = {}, []
    for m in kmods:
        ref = f'{a.name}-k{m.rsplit(".K", 1)[1]}'
        local = os.path.join(bld, rel(m))
        if ref not in tips:
            if os.path.exists(local + '.olean') and not a.require_remote:
                got[m] = 'local'
                continue
            raise SystemExit(f'part {m} not published ({SPFX}{ref})')
        repo.fetch([ref])
        fs = repo.files(ref)
        lines = {r['module']: r for r in map(json.loads, fs['manifest.jsonl'].decode().splitlines()) if r}
        for b in base:
            if lines[b]['source_sha256'] != mine[b]['source_sha256'] or lines[b]['parts']['.olean'] != mine[b]['parts']['.olean']:
                raise SystemExit(f'part {m}: built on a different {b} (source or .olean sha256 differs)')
        if lines[m]['source_sha256'] != man['sources'][m]:
            raise SystemExit(f'part {m}: source sha256 differs from the split manifest')
        for e in PARTS:
            data = fs[m + e]
            if e != '.stamp' and P.hashlib.sha256(data).hexdigest() != lines[m]['parts'][e]:
                raise SystemExit(f'part {m}{e}: sha256 differs from its manifest line')
            os.makedirs(os.path.dirname(local), exist_ok=True)
            open(local + e, 'wb').write(data)
        got[m] = json.loads(fs['record.json'])['host']
        rlogs += [json.loads(l) for l in fs['build-log.jsonl'].decode().splitlines() if l.strip()]
    fin = man['final']
    t0 = time.time()
    build(src, bld, [fin], 6.0, 1)          # every K is up to date (stamps): only the final module is compiled
    P.log(f'{a.name}: final module built in {time.time() - t0:.1f} s; parts from {got}')
    kl = {r['module']: r for r in audit_manifest(src, bld, base + kmods + [fin])}
    flog = [json.loads(l) for l in open(os.path.join(bld, 'build-log.jsonl')) if l.strip()] + rlogs
    write_record(a, man, src, bld, kl, flog, got)


def write_record(a, man, src, bld, kl, flog, got):
    """result.json as prod435.cmd_one writes it, plus the split information, and the publication."""
    fin = man['final']
    items = {it[0]: it for it in P.plan_items(a.plan)}
    mod, kind, key, level, est, name = items[fin]
    srcf = os.path.join(src, rel(fin) + '.lean')
    base = os.path.join(bld, rel(fin))
    txt = open(srcf, encoding='utf-8').read()
    stmt = txt[txt.index('public theorem refuted'):].split(':=')[0].split(' : ', 1)[1].strip()
    assert stmt == man['statement']
    rep = json.load(open(a.replay_json)) if a.replay_json else {}
    last = {}
    for r in flog:
        last[r['module']] = r
    allm = list(kl)
    res = dict(module=mod, kind=kind, key=key, level=level, name=name, plan=os.path.basename(a.plan),
               plan_est_hints=est, sched_est_hints=None, full_proof_hints=a.full_proof_hints, hints=rep.get('hints'),
               lemmas=rep.get('lemmas'), segments=rep.get('segments'), core_clauses=rep.get('core'),
               statement=stmt, imports=P.audit_header(srcf), source_sha256=P.sha(srcf),
               source_bytes=os.path.getsize(srcf),
               parts={e: P.sha(base + e) for e in P.PARTS if os.path.exists(base + e)},
               sizes={e: os.path.getsize(base + e) for e in P.PARTS if os.path.exists(base + e)},
               lean_cpu_s=round(sum(last[m]['cpu'] for m in allm if m in last), 1),
               lean_wall_s=round(max(last[m]['wall'] for m in allm if m in last), 1),
               peak_anon_gb=max(last[m]['anon_gb'] for m in allm if m in last),
               peak_rss_gb=max(last[m]['rss_gb'] for m in allm if m in last),
               seconds={}, lrat_s=rep.get('lrat_s'), producer=rep.get('producer'),
               lean=subprocess.run([P.LEAN, '--version'], capture_output=True, text=True).stdout.strip(),
               generator_commit=P.git('rev-parse', 'HEAD', cwd=ROOT).strip(),
               core_manifest_sha256=P.sha(os.path.join(P.CORE, 'core-manifest.jsonl')),
               host=socket.gethostname(), t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
               split=dict(tool='lean435/tools/split435.py + splitfarm435.py', sources_ref=f'{SPFX}src-{a.name}',
                          part_hosts=got, modules={m: {'source_sha256': kl[m]['source_sha256'], 'parts': kl[m]['parts'],
                                                       'cpu': last.get(m, {}).get('cpu'),
                                                       'anon_gb': last.get(m, {}).get('anon_gb')} for m in allm}))
    D = os.path.join(wd(a.name), 'job')
    os.makedirs(os.path.join(D, 'build', os.path.dirname(rel(fin))), exist_ok=True)
    shutil.copyfile(base + '.olean', os.path.join(D, 'build', rel(fin) + '.olean'))
    json.dump(res, open(os.path.join(D, 'result.json'), 'w'))
    print(json.dumps({k: v for k, v in res.items() if k != 'split'}))
    if a.no_publish:
        return
    publish(a, res, os.path.join(D, 'build', rel(fin) + '.olean'))


def publish(a, res, olean):
    """Append res to the helper branch <family>help/w<J> (fast-forward), as prod435 run --steal publishes."""
    repo = P.Repo(P.HELP_PFX)
    me = f'w{a.index}'
    tips = repo.ls()
    done = {}
    tip = tips.get(me)
    if tip:
        repo.fetch([me])
        for l in repo.files(me, only={'manifest.jsonl'}).get('manifest.jsonl', b'').decode().splitlines():
            if l.strip():
                r = json.loads(l)
                done[r['module']] = r
    if res['module'] in done:
        raise SystemExit(f'{res["module"]} is already published on {P.HELP_PFX}{me}')
    done[res['module']] = res
    add = {res['module'] + '.olean': open(olean, 'rb').read(),
           'manifest.jsonl': ('\n'.join(sorted(json.dumps(r, sort_keys=True) for r in done.values())) + '\n').encode(),
           'record.json': json.dumps(dict(index=a.index, workers=0, plan=os.path.basename(a.plan), host=socket.gethostname(),
                                          helper=True, done=len(done), todo=0, failed=0, running=[],
                                          note='split certificate (splitfarm435.py final)',
                                          t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))).encode()}
    c = repo.push(me, add, tip, f'splitfarm435 {me}: {res["module"]} (split certificate)')
    P.log(f'published {res["module"]} -> {P.HELP_PFX}{me} {c[:10]}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('pack')
    p.add_argument('--src', required=True)
    p.add_argument('--name', required=True)
    p = sub.add_parser('part')
    p.add_argument('--name', required=True)
    p.add_argument('--k', type=int, action='append', required=True)
    p.add_argument('--rss-gb', type=float, default=7.0, help='RssAnon cap per part (two parts run at once)')
    p.add_argument('--jobs', type=int, default=4)
    p = sub.add_parser('final')
    p.add_argument('--name', required=True)
    p.add_argument('--plan', required=True)
    p.add_argument('--index', type=int, required=True)
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--replay-json', default=None)
    p.add_argument('--full-proof-hints', type=int, default=None)
    p.add_argument('--require-remote', action='store_true', help='every part from its branch (no local part)')
    p.add_argument('--no-publish', action='store_true')
    p = sub.add_parser('status')
    p.add_argument('--name', required=True)
    a = ap.parse_args()
    {'pack': cmd_pack, 'part': cmd_part, 'final': cmd_final, 'status': cmd_status}[a.cmd](a)


if __name__ == '__main__':
    main()
