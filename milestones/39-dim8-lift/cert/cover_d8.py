#!/usr/bin/env python3
"""Cover worker: the 36 cover certificates on ordinary (16 GB) machines, by splitting each cover CNF.

    cover_d8.py run --stack DIR --work DIR [--index I[,J|-K] --workers W] [--only c5,R5,...] [--depth 2]
                    [--mem-gb 12] [--procs 2] [--publish] [--name kI] [--max-depth 6] [--hours H]

Needs scripts/make_tables.sh (lean/gen, lean/build with TabAll) and a stack with Walk, WalkSplit and TabAll
(prod_d8.py setup ports them when lean/gen exists; this script runs it if they are missing).
Items: 'c5' (CoverKC5: Unsat (c5Cnf (t5.map (·.1)))) and the 35 Q5 representatives R5 (CoverKC6R<R5>:
Unsat (c6Cnf R5 ((t6.filter (·.1 == R5)).map (·.2.1)))), sharded by sha1(module) % W.
Why split: the whole cover is 14 M hints with a 98 k-clause core (a > 12 GB replay); unit clauses on its most
frequent variables shrink it (c5 measured: depth 1 8.2-8.6 M hints, depth 2 3.5-4.5 M, depth 3 1.5-2.2 M), and
make_cover_cert.py's split walk keeps every walk module <= 5.7 GB (leaf c5 [2,3]: peak 5.7 GB, ~1.7 h).
Per cover:
  1. order        the CNF's variables by occurrence count (descending, then index), from CovExport.lean;
  2. leaves       the 2^d paths on the first d variables (d = --depth); a leaf p is made by make_cover_cert.py
                  (UNITS=p, LEAF=<bits>): Unsat (Dim8Lift.Split.units p ++ FULL). A leaf whose solve hits the cap or
                  whose predicted peak max(6, 1.25 pred_gb) exceeds --mem-gb is split on the next variable;
                  at most --procs leaves at once under prod_d8.py's memory reservation; built leaves are reused;
  3. top          Cover<mod>.lean: Dim8Lift.Split.unsat_of_leaves FULL T (by decide) ls (by decide) <leaf certs>,
                  then a public check from a clean directory (statement over c5Cnf / c6Cnf R5, standard axioms);
  4. record       an OK line (module CoverKC5 / CoverKC6R<R5>, route cover-split) in WORK/manifest.jsonl and the
                  public .olean in WORK/olean; --publish pushes both to <ref-prefix>/<name> (default k<first index>)
                  with prod_d8.publish, where assemble_d8.py collects them. A SAT leaf records SAT? and stops.
"""
import argparse, hashlib, itertools, json, os, shutil, socket, sys, time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import prod_d8 as P
import tail_d8 as T
LEAN = P.LEAN; LEANDIR = os.path.join(P.M, 'lean')
Q5REPS = None


def q5reps():
    global Q5REPS
    if Q5REPS is None:
        r = P.sh([LEAN, '--run', 'CovExport.lean', 'list5'], cwd=LEANDIR, env=dict(os.environ, LEAN_PATH=os.path.join(LEANDIR, 'build')))
        assert r.returncode == 0, r.stderr
        Q5REPS = [int(x) for x in r.stdout.split()]; assert len(Q5REPS) == 35
    return Q5REPS


def mod_of(w): return 'KC5' if w == 'c5' else 'KC6R%d' % int(w)


def full_of(w):
    if w == 'c5': return 'Dim8Lift.Tab.c5Cnf (Dim8Lift.Tab.t5.map (·.1))'
    return 'Dim8Lift.Tab.c6Cnf %d ((Dim8Lift.Tab.t6.filter (·.1 == %d)).map (·.2.1))' % (int(w), int(w))


def var_order(a, w, cd):
    f = os.path.join(cd, 'order.json')
    if os.path.exists(f): return json.load(open(f))
    cnf = os.path.join(cd, 'full.cnf')
    P.sh([LEAN, '--run', 'CovExport.lean'] + (['c5'] if w == 'c5' else ['c6', w]) + [cnf], cwd=LEANDIR,
         env=dict(os.environ, LEAN_PATH=os.path.join(LEANDIR, 'build')))
    c = Counter()
    for l in open(cnf):
        if l.startswith('p'): continue
        c.update(abs(int(x)) for x in l.split()[:-1])
    os.remove(cnf)
    o = [v for v, _ in sorted(c.items(), key=lambda x: (-x[1], x[0]))][:32]
    json.dump(o, open(f, 'w')); return o


def leaf_job(a, w, cd, p, held):
    m = mod_of(w) + 'L' + T.bits(p); d = os.path.join(cd, 'leaves', m); gj = os.path.join(d, 'gen.json')
    olean = os.path.join(d, 'build', 'Cover' + m + '.olean')
    if os.path.exists(olean) and os.path.exists(gj): return 'done', json.load(open(gj))
    P.reserve(held[0], P.GEN_GB); held[0] = P.GEN_GB
    if not (os.path.exists(gj) and os.path.exists(os.path.join(d, 'gen', m + '.modules'))):
        shutil.rmtree(d, ignore_errors=True); os.makedirs(d)
        lim = max(300.0, (a.mem_gb - 3.1) / 0.55 * 1e6 / 28000)
        r = P.sh([sys.executable, os.path.join(HERE, 'make_cover_cert.py'), w, d], cwd=HERE,
                 env=dict(os.environ, UNITS=','.join(map(str, p)), LEAF=T.bits(p), SOLVE_LIMIT=str(round(lim))))
        if r.returncode == 10: return 'SAT', {}
        if r.returncode == 11: shutil.rmtree(d, ignore_errors=True); return 'split', {'solve_limit': round(lim)}
        if r.returncode != 0: return 'failed', {'log': (r.stdout + r.stderr)[-1500:]}
        g = json.loads(r.stdout.strip().splitlines()[-1])
        info = dict(hints=g['replay']['hints'], vars=g['core']['vars'], core=g['core']['core'], solve_s=g['solve_s'], gen_s=g['gen_s'])
        # measured: leaf c5 [2,3] (3.54 M hints, 12.5 k vars) replay 5.66 GB (model 5.1), walk modules <= 5.7 GB
        info['pred_gb'] = round(max(6.0, 1.25 * P.pred_gb(info['hints'], info['vars'])), 1)
        if info['pred_gb'] > a.mem_gb: shutil.rmtree(d, ignore_errors=True); return 'split', info
        json.dump(info, open(gj, 'w'))
    info = json.load(open(gj))
    P.reserve(held[0], info['pred_gb']); held[0] = info['pred_gb']
    t = time.time()
    r = P.sh(['bash', os.path.join(HERE, 'build_cert.sh'), d, m], env=dict(os.environ, STACK=os.path.join(a.stack, 'build'), JOBS='1'))
    rss = [int(x.split()[0]) for x in r.stdout.split(' s ')[1:] if x.split()[0].isdigit()]
    info.update(build_s=round(time.time() - t, 1), peak_mb=max(rss) if rss else None)
    if 'CERT BUILT' not in r.stdout or not os.path.exists(olean): return 'failed', {'log': r.stdout[-1500:]}
    shutil.rmtree(os.path.join(d, 'gen'), ignore_errors=True); shutil.rmtree(os.path.join(d, 'work'), ignore_errors=True)
    json.dump(info, open(gj, 'w'))
    return 'done', info


def run_leaf(a, w, cd, p):
    held = [0.0]
    try:
        return leaf_job(a, w, cd, p, held)
    except Exception as e:   # noqa: a crashed leaf fails the cover, not the worker
        return 'failed', {'log': repr(e)[-1500:]}
    finally:
        with P.BLOCK:
            P.BUDGET['used'] -= held[0]; P.BLOCK.notify_all()


def public_closure(stack, roots):
    b = os.path.join(stack, 'build'); arts = {}; todo = list(roots)
    while todo:
        m = todo.pop()
        if m in arts or m in ('Std', 'Init', 'Lean'): continue
        arts[m] = [[os.path.join(b, m + '.olean')], []]
        for l in open(os.path.join(stack, m + '.lean')):
            if l.startswith('public import '): todo.append(l.split()[2])
    return arts


def check_public(a, w, olean, cd):
    mod = 'Cover' + mod_of(w); ns = 'Snake9.CoverCert.' + mod_of(w)
    d = os.path.join(cd, 'pubcheck'); os.makedirs(d, exist_ok=True)
    shutil.copyfile(olean, os.path.join(d, mod + '.olean'))
    arts = public_closure(a.stack, ['CoverDefs', 'TabAll']); arts[mod] = [[os.path.join(d, mod + '.olean')], []]
    open(os.path.join(d, 'Chk.lean'), 'w').write('module\n\nimport %s\n\n#check @%s.unsat\n#print axioms %s.unsat\n' % (mod, ns, ns))
    json.dump(dict(name='Chk', isModule=True, importArts=arts, dynlibs=[], plugins=[], options={}), open(os.path.join(d, 'setup.json'), 'w'))
    r = P.sh([LEAN, '--setup', 'setup.json', 'Chk.lean'], cwd=d, env=dict(os.environ, LEAN_PATH='/nonexistent'))
    out = r.stdout + r.stderr
    stmt = 'c5Cnf (List.map' if w == 'c5' else 'c6Cnf %s' % w
    ok = (r.returncode == 0 and 'depends on axioms: [propext, Classical.choice, Quot.sound]' in out
          and stmt in out and 'units' not in out and 'sorry' not in out)
    return ok, out.strip()


def cover(a, w, stop):
    mod = mod_of(w); cd = os.path.join(a.work, 'jobs', 'Cover' + mod); os.makedirs(cd, exist_ok=True)
    t0 = time.time(); rec = dict(module='Cover' + mod, which=w, host=socket.gethostname(), commit=a.commit, route='cover-split', mem_gb=a.mem_gb)
    order = var_order(a, w, cd); sf = os.path.join(cd, 'state.json')
    st = json.load(open(sf)) if os.path.exists(sf) else \
        {T.key([s * v for s, v in zip(sg, order[:a.depth])]): 'todo' for sg in itertools.product((1, -1), repeat=a.depth)}
    save = lambda: json.dump(st, open(sf + '.tmp', 'w')) or os.replace(sf + '.tmp', sf)
    save(); infos = {}
    with ThreadPoolExecutor(a.procs) as ex:
        fut = {}
        while True:
            for s_, v_ in list(st.items()):
                if v_ == 'todo' and s_ not in fut.values() and not stop():
                    fut[ex.submit(run_leaf, a, w, cd, T.path(s_))] = s_
            if not fut: break
            dn, _ = wait(list(fut), return_when=FIRST_COMPLETED)
            for f in dn:
                s_ = fut.pop(f); p = T.path(s_); res, info = f.result()
                if res == 'done': st[s_] = 'done'; infos[s_] = info
                elif res == 'split':
                    if len(p) >= a.max_depth: st[s_] = 'todo'; rec.update(status='FAILED', log='leaf %s too big at depth %d' % (s_, len(p)))
                    else: v = order[len(p)]; st[s_] = 'split'; st[T.key(p + [v])] = 'todo'; st[T.key(p + [-v])] = 'todo'
                elif res == 'SAT': st[s_] = 'SAT'; rec.update(status='SAT?', leaf=p)
                else: st[s_] = 'todo'; rec.update(status='FAILED', leaf=p, log=info.get('log'))
                save()
            if rec.get('status'):
                for f in list(fut): f.result()
                break
    if rec.get('status'): return rec
    if stop() or any(v_ == 'todo' for v_ in st.values()): return None
    leaves = [tuple(T.path(s_)) for s_, v_ in st.items() if v_ == 'done']
    for s_ in st:
        if st[s_] == 'done' and s_ not in infos:
            infos[s_] = json.load(open(os.path.join(cd, 'leaves', mod + 'L' + T.bits(T.path(s_)), 'gen.json')))
    tree, order_ = T.tree_of(leaves)
    names = [mod + 'L' + T.bits(p) for p in order_]
    top = os.path.join(cd, 'top'); os.makedirs(top, exist_ok=True)
    ls = '[%s]' % ', '.join('[%s]' % ', '.join('(%d : Int)' % x for x in p) for p in order_)
    cert = '⟨%s, trivial⟩' % ', '.join('Snake9.CoverCert.%s.unsat' % n for n in names)
    src = ('module\n\npublic import CoverDefs\npublic import TabAll\nimport Split\n%s\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
           'namespace Snake9.CoverCert.%s\nopen Dim8Lift.Split\n'
           'def T : ST := %s\n'
           '/-- the split cover certificate: %d leaves on the most frequent variables -/\n'
           'public theorem unsat : Snake9.LocalWindow.Unsat (%s) :=\n'
           '  unsat_of_leaves _ T (by decide) %s (by decide)\n    %s\nend Snake9.CoverCert.%s\n'
           '#print axioms Snake9.CoverCert.%s.unsat\n'
           % (''.join('import Cover%s\n' % n for n in names), mod, tree, len(names), full_of(w), ls, cert, mod, mod))
    open(os.path.join(top, 'Cover' + mod + '.lean'), 'w').write(src)
    lp = ':'.join([os.path.join(cd, 'leaves', n, 'build') for n in names] + [os.path.join(a.stack, 'build')])
    olean = os.path.join(top, 'Cover' + mod + '.olean')
    r = P.sh([LEAN, '--root=.', '-o', olean, 'Cover' + mod + '.lean'], cwd=top, env=dict(os.environ, LEAN_PATH=lp))
    lv = [infos[T.key(p)] for p in order_]
    rec.update(leaves=len(names), depth=max(len(p) for p in order_), hints=sum(x['hints'] for x in lv),
               max_leaf_hints=max(x['hints'] for x in lv), peak_mb=max([x.get('peak_mb') or 0 for x in lv]),
               splits=sum(1 for v_ in st.values() if v_ == 'split'), order=order[:max(len(p) for p in order_)])
    if r.returncode != 0 or not os.path.exists(olean):
        rec.update(status='BUILD_FAILED', log=(r.stdout + r.stderr)[-1500:]); return rec
    ok, out = check_public(a, w, olean, cd)
    if not ok: rec.update(status='CHECK_FAILED', log=out[-1500:]); return rec
    dst = os.path.join(a.work, 'olean', 'Cover' + mod + '.olean'); os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copyfile(olean, dst)
    rec.update(status='OK', sha256=hashlib.sha256(open(dst, 'rb').read()).hexdigest(), total_s=round(time.time() - t0, 1))
    shutil.rmtree(cd, ignore_errors=True)
    return rec


def ensure_stack(a):
    T.ensure_stack(a)
    b = os.path.join(a.stack, 'build')
    if not all(os.path.exists(os.path.join(b, m + '.olean')) for m in ('Walk', 'WalkSplit', 'TabAll')):
        assert os.path.exists(os.path.join(LEANDIR, 'gen', 'TabAll.lean')), 'run scripts/make_tables.sh first'
        r = P.sh([sys.executable, os.path.join(HERE, 'prod_d8.py'), 'setup', '--stack', a.stack]); assert r.returncode == 0, r.stdout[-2000:] + r.stderr[-2000:]


def cmd_run(a):
    a.work = os.path.abspath(a.work); a.stack = os.path.abspath(a.stack); os.makedirs(a.work, exist_ok=True)
    a.indices = set()
    for part in a.index.split(','):
        lo, _, hi = part.partition('-'); a.indices.update(range(int(lo), int(hi or lo) + 1))
    assert a.indices and max(a.indices) < a.workers, 'indices must be < --workers'
    a.name = a.name or 'k%d' % min(a.indices)
    a.commit = P.sh(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT).stdout.strip()
    ensure_stack(a)
    man = os.path.join(a.work, 'manifest.jsonl')
    done = {r['module'] for r in map(json.loads, open(man)) if r['status'] in ('OK', 'SAT?')} if os.path.exists(man) else set()
    its = a.only.split(',') if a.only else ['c5'] + [str(r) for r in q5reps()]
    if not a.only: its = [w for w in its if int(hashlib.sha1(('Cover' + mod_of(w)).encode()).hexdigest(), 16) % a.workers in a.indices]
    its = [w for w in its if 'Cover' + mod_of(w) not in done]
    print('cover worker %s (indices %s of %d): %d covers to do, %d done' % (a.name, a.index, a.workers, len(its), len(done)), flush=True)
    P.BUDGET['cap'] = a.mem_gb; end = time.time() + a.hours * 3600
    stop = lambda: os.path.exists(os.path.join(a.work, 'STOP')) or time.time() > end
    for w in its:
        if stop(): break
        print('cover', w, time.ctime(), flush=True)
        rec = cover(a, w, stop)
        if rec is None: break
        open(man, 'a').write(json.dumps(rec) + '\n'); print(json.dumps(rec), flush=True)
        if a.publish: P.publish(a)
        if rec['status'] == 'SAT?':
            open(os.path.join(a.work, 'STOP'), 'w').write('SAT? ' + rec['module']); break
    print('cover worker finished', flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); sp = ap.add_subparsers(dest='cmd', required=True)
    r = sp.add_parser('run')
    for x in ('--stack', '--work'): r.add_argument(x, required=True)
    r.add_argument('--index', default='0'); r.add_argument('--workers', type=int, default=1); r.add_argument('--name', default='')
    r.add_argument('--mem-gb', type=float, default=12); r.add_argument('--procs', type=int, default=2)
    r.add_argument('--depth', type=int, default=2); r.add_argument('--max-depth', type=int, default=6)
    r.add_argument('--only', default=''); r.add_argument('--publish', action='store_true')
    r.add_argument('--hours', type=float, default=1e6); r.add_argument('--ref-prefix', default='refs/heads/xfer/d8')
    a = ap.parse_args()
    {'run': cmd_run}[a.cmd](a)
