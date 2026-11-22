#!/usr/bin/env python3
"""Split certificate of one hard cube: Unsat (cubeCnfQ 13 L A k) from leaf certificates.

    python3 make_split.py L Ahex k OUT [--t0 60] [--force D] [--jobs 3] [--stack DIR] [--march BIN [--march-args "-d 4"]]

1. search   scripts/split.py on the Lean-exported cubeCnfQ (ENC=q): every node is solved with a time
            limit t0; an unfinished node is split on the next vertex variable (positive branch first).
            The UNSAT nodes are the leaves; a SAT leaf stops everything (exit 10).
            With --march: scripts/march_split.py instead (march_cu lookahead cubes, the trie completed
            with the siblings march refuted; --t0 then only sizes the leaves, 0 = do not pre-solve).
2. leaves   make_cert.py with UNITS=<path> LEAF=<i> for each leaf:
              Unsat (Dim8Lift.Split.units path ++ cubeCnfQ 13 L A k)      module CubeQ<A>L<i>
            built with build_cert.sh against the stack, at most --jobs at a time (memory: one 10 M-hint
            leaf is ~9 GB, so keep leaves short with t0).
3. top      CubeQ<A>.lean: the split tree `T : ST` (from the leaf paths), `T.leaves = [paths]` by decide,
            `public theorem unsat : Unsat (cubeCnfQ 13 L A k)` by `Split.unsat_of_leaves`; the leaf
            modules are private imports, so the top's public .olean is the same interface as an
            ordinary cube certificate.
Resumable: finished searches (nodes.jsonl with a final line) and built leaves are reused.
"""
import argparse, json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__)); M = os.path.abspath(os.path.join(HERE, '..'))
LEAN = '/opt/lean-4.35.0-linux/bin/lean'
ap = argparse.ArgumentParser()
ap.add_argument('L', type=int); ap.add_argument('A'); ap.add_argument('k', type=int); ap.add_argument('out')
ap.add_argument('--t0', type=int, default=60); ap.add_argument('--force', type=int, default=0); ap.add_argument('--jobs', type=int, default=3)
ap.add_argument('--stack', default=os.path.expanduser('~/d8stack'))
ap.add_argument('--march', default='', help='march_cu binary: cube with scripts/march_split.py instead of split.py')
ap.add_argument('--march-args', default='-d 4', help='march_cu options (e.g. "-d 4", "-n 2000", "-l 64")')
a = ap.parse_args()
out = os.path.abspath(a.out); os.makedirs(out, exist_ok=True)
mask = int(a.A, 16); verts = [u for u in range(64) if mask >> u & 1]; assert len(verts) == a.k
mod = 'Q' + a.A.upper(); t0 = time.time(); stats = dict(module='Cube' + mod, A=a.A, k=a.k, L=a.L, t0=a.t0)

# 1. search
sd = os.path.join(out, 'search'); os.makedirs(sd, exist_ok=True)
json.dump(verts, open(os.path.join(sd, 'A.json'), 'w'))
res = os.path.join(sd, 'result.json')
if not os.path.exists(res) and a.march:
    r = subprocess.run([sys.executable, os.path.join(M, 'scripts', 'march_split.py'), str(a.L), str(a.k), os.path.join(sd, 'A.json'),
                        sd, str(a.t0), str(a.jobs), a.march] + a.march_args.split(), capture_output=True, text=True)
    assert r.returncode == 0, (r.stdout + r.stderr)[-1000:]
    last = json.loads(r.stdout.strip().splitlines()[-1]); json.dump(last, open(res, 'w'))
if not os.path.exists(res):
    r = subprocess.run([sys.executable, os.path.join(M, 'scripts', 'split.py'), '8', '13', str(a.L), '6', os.path.join(sd, 'A.json'),
                        sd, str(a.t0), str(a.jobs)], capture_output=True, text=True, env=dict(os.environ, GEN='lean', ENC='q', FORCE=str(a.force)))
    last = json.loads(r.stdout.strip().splitlines()[-1]); json.dump(last, open(res, 'w'))
last = json.load(open(res)); stats['search'] = last
nodes = [json.loads(l) for l in open(os.path.join(sd, 'nodes.jsonl'))]
if any(n['status'] == 'SATISFIABLE' for n in nodes):
    print(json.dumps(dict(stats, status='SATISFIABLE'))); sys.exit(10)
assert last['result'] == 'UNSAT', last
# split.py: the UNSAT nodes; march_split.py: every leaf (CUBE / UNKNOWN leaves are solved by make_cert.py)
leaves = sorted({tuple(n['lits']) for n in nodes if n['status'] in ('UNSATISFIABLE', 'CUBE', 'UNKNOWN') and (n.get('src') or n['status'] == 'UNSATISFIABLE')})
stats['leaves'] = len(leaves)

# the tree from the leaf paths (positive branch first, as split.py and ST.leaves)
def build(prefix, paths):
    if paths == [prefix]: return 'ST.leaf', [prefix]
    nxt = {p[len(prefix)] for p in paths}
    v = abs(next(iter(nxt))); assert nxt <= {v, -v} and v > 0, (prefix, nxt)
    ps = [p for p in paths if p[len(prefix)] == v]; ns = [p for p in paths if p[len(prefix)] == -v]
    tp, lp = build(prefix + (v,), ps); tn, ln = build(prefix + (-v,), ns)
    return 'ST.node %d (%s) (%s)' % (v, tp, tn), lp + ln
tree, order = build((), list(leaves))
assert sorted(order) == leaves

# 2. leaves
def leaf(i):
    p = order[i]; m = mod + 'L%d' % i; d = os.path.join(out, 'leaves', m)
    if os.path.exists(os.path.join(d, 'build', 'Cube' + m + '.olean')): return m, 'reused', 0
    s = time.time()
    if not os.path.exists(os.path.join(d, 'gen', m + '.modules')):   # generated already: resume the build only
        r = subprocess.run([sys.executable, os.path.join(HERE, 'make_cert.py'), str(a.L), a.A, str(a.k), d], capture_output=True, text=True,
                           env=dict(os.environ, UNITS=','.join(map(str, p)), LEAF=str(i)))
        if r.returncode != 0: return m, 'GEN_FAILED ' + (r.stdout + r.stderr)[-500:], 0
    # leaves run --jobs at a time; inside a leaf, split-replay parts run one at a time (a late part peaks
    # like the whole leaf replay), unless LEAF_JOBS says otherwise
    b = subprocess.run(['bash', os.path.join(HERE, 'build_cert.sh'), d, m], capture_output=True, text=True,
                       env=dict(os.environ, STACK=os.path.join(a.stack, 'build'), JOBS=os.environ.get('LEAF_JOBS', '1')))
    open(os.path.join(d, 'build.log'), 'w').write(b.stdout)
    if 'CERT BUILT' not in b.stdout: return m, 'BUILD_FAILED ' + b.stdout[-500:], 0
    return m, 'OK', round(time.time() - s)
with ThreadPoolExecutor(a.jobs) as ex:
    done = list(ex.map(leaf, range(len(order))))
bad = [d for d in done if d[1] not in ('OK', 'reused')]
stats['leaf_s'] = sum(d[2] for d in done)
if bad:
    print(json.dumps(dict(stats, status='LEAF_FAILED', failed=bad[:5]))); sys.exit(1)

# 3. top module, built in a directory that holds every leaf build
top = os.path.join(out, 'top'); os.makedirs(top, exist_ok=True)
ls = '[%s]' % ', '.join('[%s]' % ', '.join('(%d : Int)' % x for x in p) for p in order)
cert = '⟨%s, trivial⟩' % ', '.join('Snake9.CubeProv.%sL%d.unsat' % (mod, i) for i in range(len(order)))
src = ('module\n\npublic import CubeCnf\nimport Split\n%s\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
       'namespace Snake9.CubeProv.%s\nopen Dim8Lift.Split\n'
       'def T : ST := %s\n'
       '/-- the split certificate: %d leaves of the vertex-literal split tree -/\n'
       'public theorem unsat : Snake9.LocalWindow.Unsat (Dim8Lift.Cube.cubeCnfQ 13 %d 0x%s %d) :=\n'
       '  unsat_of_leaves _ T (by decide) %s (by decide)\n    %s\nend Snake9.CubeProv.%s\n'
       '#print axioms Snake9.CubeProv.%s.unsat\n'
       % (''.join('import Cube%sL%d\n' % (mod, i) for i in range(len(order))), mod, tree, len(order), a.L, a.A, a.k, ls, cert, mod, mod))
open(os.path.join(top, 'Cube' + mod + '.lean'), 'w').write(src)
lp = ':'.join([os.path.join(out, 'leaves', mod + 'L%d' % i, 'build') for i in range(len(order))] + [os.path.join(a.stack, 'build')])
s = time.time()
r = subprocess.run([LEAN, '--root=.', '-o', os.path.join(top, 'Cube' + mod + '.olean'), 'Cube' + mod + '.lean'], cwd=top,
                   capture_output=True, text=True, env=dict(os.environ, LEAN_PATH=lp))
o = r.stdout + r.stderr
ok = r.returncode == 0 and 'depends on axioms: [propext, Classical.choice, Quot.sound]' in o
stats.update(top_s=round(time.time() - s), total_s=round(time.time() - t0), status='OK' if ok else 'TOP_FAILED')
if not ok: stats['log'] = o[-1500:]
print(json.dumps(stats))
sys.exit(0 if ok else 1)
