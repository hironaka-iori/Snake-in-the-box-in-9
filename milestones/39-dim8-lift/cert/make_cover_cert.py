"""One cover certificate as Lean 4.35 modules:
  python3 make_cover_cert.py c5 OUT          Unsat (c5Cnf (t5.map (·.1)))
  python3 make_cover_cert.py R5 OUT          Unsat (c6Cnf R5 ((t6.filter (·.1 == R5)).map (·.2.1)))   (R5 one of the 35 q5reps)
Steps: Lean export (CovExport.lean), cadical --lrat, core compaction (pilot.py), v3 replay (genv3stream), then
  - W_i (one per 4,000-clause chunk R_i): the core clauses with their 0-based index in the full CNF, Nat codes,
    and `renN tree.get r_i (w_i.map Prod.snd) = true` (the compaction renaming, as in make_cert.py);
  - Core (core := w_0 ++ ...) and K<g> modules: the walk split by FULL's parts (cUnits, cDeg, cLvl, cCtrs, one cBlk
    per table chunk), `walkN P_k o_k ((core.drop d_k).take n_k) = true` per part by `decide +kernel`, grouped
    by WALK_GROUP (6,000) clauses (one kernel evaluation of the whole cover needs > 13.6 GB);
  - the top module: walk_ok by WalkSplit.walkN_step over the parts (FULL rewritten right-nested by simp) and
    `public theorem unsat : Unsat FULL` by `Walk.unsat_of_walkN`.
Needs lean/build (plain stack with TabAll and Walk) for the export; builds against the module stack.
Split leaves (as make_cert.py): UNITS="l1,l2,..." and LEAF=<bits> give module Cover<mod>L<bits> with
  public theorem unsat : Unsat (Dim8Lift.Split.units [l1, ...] ++ FULL)
(the exported CNF is the unit clauses followed by FULL, so walkN indices are positions in `units ps ++ FULL`);
the cover top module is then Dim8Lift.Split.unsat_of_leaves FULL (cover_d8.py builds it). SOLVE_LIMIT (s) as in
make_cert.py: exit 11 at the cap."""
import sys, os, subprocess, json, time
which, out = sys.argv[1], sys.argv[2]
HERE = os.path.dirname(os.path.abspath(__file__)); M = os.path.join(HERE, '..'); LEANDIR = os.path.join(M, 'lean')
ROOT = os.path.abspath(os.path.join(M, '..', '..')); LEAN = '/opt/lean-4.35.0-linux/bin/lean'
US = [int(x) for x in os.environ.get('UNITS', '').split(',') if x.strip()]; LEAF = os.environ.get('LEAF', '')
assert bool(US) == bool(LEAF), 'UNITS and LEAF go together'
import re
TABALL = open(os.path.join(LEANDIR, 'gen', 'TabAll.lean')).read()
chunks = lambda t: re.search(r'^def %s : [^=]*:= (.*)$' % t, TABALL, re.M).group(1).split(' ++ ')
if which == 'c5':
    mod = 'KC5'; FULL = 'Dim8Lift.Tab.c5Cnf (Dim8Lift.Tab.t5.map (·.1))'; exp = ['c5']
    PARTS = ['cUnits []', 'cDeg 5', 'cLvl 5', 'cCtrs cbase [(unsel5, 17)]'] + \
            ['cBlk 5 (List.map (fun e => e.1) %s)' % c_ for c_ in chunks('t5')]
    SIMP = 'c5Cnf, coverCnf, t5, List.map_append, cBlk_append, List.append_assoc'
else:
    r5 = int(which); mod = 'KC6R%d' % r5
    FULL = 'Dim8Lift.Tab.c6Cnf %d ((Dim8Lift.Tab.t6.filter (·.1 == %d)).map (·.2.1))' % (r5, r5); exp = ['c6', str(r5)]
    PARTS = ['cUnits ((List.range 32).map fun u => (u, Nat.testBit %d u))' % r5, 'cDeg 6', 'cLvl 6',
             'cCtrs cbase [(selB, pcN 32 %d), (unselB, 32 - (29 - pcN 32 %d))]' % (r5, r5)] + \
            ['cBlk 6 (List.map (fun e => e.2.1) (List.filter (fun e => e.1 == %d) %s))' % (r5, c_) for c_ in chunks('t6')]
    SIMP = 'c6Cnf, coverCnf, t6, List.filter_append, List.map_append, cBlk_append, List.append_assoc'

if US:
    PARTS = ['Dim8Lift.Split.units [%s]' % ', '.join('(%d : Int)' % x for x in US)] + PARTS
    mod += 'L' + LEAF; FULL = '(Dim8Lift.Split.units [%s] ++ %s)' % (', '.join('(%d : Int)' % x for x in US), FULL)
W = os.path.join(out, 'work', mod); os.makedirs(W, exist_ok=True)
env = dict(os.environ, LEAN_PATH=os.path.join(LEANDIR, 'build'))
t0 = time.time(); stats = dict(module=mod, which=which)
cnf = os.path.join(W, 'f.cnf'); lrat = os.path.join(W, 'f.lrat')
subprocess.run([LEAN, '--run', 'CovExport.lean'] + exp + [cnf], cwd=LEANDIR, env=env, check=True)
OPEN = 'open Dim8Lift Dim8Lift.Cover Dim8Lift.Tab'
lr = os.path.join(W, 'PartLen.lean')
open(lr, 'w').write('import TabAll\nimport CoverDefs\nimport Split\n%s\ndef main : IO Unit := do\n%s\n'
                    % (OPEN, '\n'.join('  IO.println (%s).length' % p_ for p_ in PARTS)))
PLEN = [int(x) for x in subprocess.run([LEAN, '--run', lr], cwd=LEANDIR, env=env, check=True, capture_output=True, text=True).stdout.split()]
assert len(PLEN) == len(PARTS)
if US:   # the leaf CNF: the unit clauses first, then FULL (the order of `units ps ++ FULL`, for walkN)
    body = open(cnf).read().split('\n', 1); hd = body[0].split()
    open(cnf, 'w').write('p cnf %s %d\n' % (hd[2], int(hd[3]) + len(US)) + ''.join('%d 0\n' % x for x in US) + body[1])
s = time.time()
lim = float(os.environ.get('SOLVE_LIMIT', '0'))
try:
    r = subprocess.run(['cadical', '-q', '--lrat', '--binary=false', cnf, lrat], capture_output=True, text=True, timeout=lim or None)
except subprocess.TimeoutExpired:
    for f_ in (lrat, cnf):
        if os.path.exists(f_): os.remove(f_)
    print(json.dumps(dict(stats, status='TOO_BIG', solve_limit=lim))); sys.exit(11)
stats['solve_s'] = round(time.time() - s, 1)
if 's SATISFIABLE' in r.stdout:
    print(json.dumps(dict(stats, status='SATISFIABLE'))); sys.exit(10)   # the cover would be wrong: report, never certify
assert 's UNSATISFIABLE' in r.stdout, r.stdout[:200]
gen = os.path.join(out, 'gen'); os.makedirs(gen, exist_ok=True)
c = json.loads(subprocess.run(['python3', os.path.join(HERE, 'pilot.py'), cnf, lrat, mod, gen], capture_output=True, text=True, check=True).stdout)
stats.update(core=c)
os.remove(lrat)   # the original LRAT (up to ~10 GB) is no longer needed: genv3stream reads the compacted gen/<mod>.lrat
g = json.loads(subprocess.run(['python3', os.path.join(ROOT, 'lean435', 'tools', 'genv3stream.py'), '--work', gen, '--data', os.path.join(gen, 'core'),
                               '--out', gen, '--off', str(c['vars'] + 1), '--seg', str(max(60000, -(-c['hints'] // 4000))), mod],
                              capture_output=True, text=True, check=True).stdout.strip().splitlines()[-1])
# --seg: the v3 reference format has a 12-bit segment field (< 4095 segments); at the default 60 k hints per
# segment, k = 30 cube 1669966996966929 (296 M hints) failed, so segments grow with the hint count
stats['replay'] = {x: g[x] for x in ('lemmas', 'hints', 'segments', 'wbits', 'off', 'lean_bytes')}
os.remove(os.path.join(gen, mod + '.lrat'))   # the compacted LRAT, now in the replay modules
glue = json.load(open(os.path.join(gen, mod + '.glue.json')))
core = glue['core_ids']; cs = set(core)
assert core == sorted(core) and len(core) == len(cs), 'core ids must be increasing (walk order)'
enc = lambda l: 2 * abs(l) + (0 if l > 0 else 1)
rows = {}; i = 0
for line in open(cnf):
    if line.startswith('p'): continue
    i += 1
    if i in cs:
        rows[i] = '(%d, [%s])' % (i - 1, ', '.join(str(enc(int(x))) for x in line.split()[:-1]))
stats['full_clauses'] = i
assert sum(PLEN) == i, ('part lengths', sum(PLEN), i)
os.remove(cnf)
CH = 4000   # pilot.py's chunk size
rparts = open(os.path.join(gen, 'LocalWindowCnf', mod + '.parts')).read().split()
pd = os.path.join(gen, 'CoverCert', mod); os.makedirs(pd, exist_ok=True)
ordered = [rows[c_] for c_ in core]
parts = ['W%d' % (j // CH) for j in range(0, len(ordered), CH)]
assert len(parts) == len(rparts), (parts, rparts)
back = glue['back']; N = len(back)
SUB = []
def tree(i0, step, depth=0):
    if i0 + step > N: return 'BT.lf %d' % (back[i0 - 1] if 1 <= i0 <= N else 0)
    if depth == 7:
        SUB.append('def s%d : BT := %s' % (len(SUB), tree(i0, step, 8 + depth))); return 's%d' % (len(SUB) - 1)
    return 'BT.nd (%s) (%s)' % (tree(i0, 2 * step, depth + 1), tree(i0 + step, 2 * step, depth + 1))
NS = 'Snake9.CoverCert.' + mod; LW = 'Snake9.LocalWindow.' + mod
HDR = "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
top = tree(0, 1)
open(os.path.join(pd, 'Tree.lean'), 'w').write("module\n\nimport RenN\n\n%snamespace %s\nopen Dim8Lift.RenN\n%s\ndef tree : BT := %s\nend %s\n"
                                              % (HDR, NS, '\n'.join(SUB), top, NS))
for j, nm in enumerate(parts):
    open(os.path.join(pd, nm + '.lean'), 'w').write(
        "module\n\nimport RenN\nimport all CoverCert.%s.Tree\nimport all LocalWindowCnf.%s.%s\n\n%snamespace %s\nopen Dim8Lift.RenN\n"
        "def w%d : List (Nat × List Nat) := [\n%s]\n"
        "theorem n%d : renN tree.get %s.r%d (w%d.map Prod.snd) = true := by decide +kernel\nend %s\n"
        % (mod, mod, rparts[j], HDR, NS, j, ",\n".join(ordered[j * CH:(j + 1) * CH]), j, LW, j, j, NS))
ren = 'n0'
for j in range(1, len(parts)): ren = 'renN_app _ (%s) n%d' % (ren, j)
P = ' ++ '.join('w%d' % j for j in range(len(parts)))
# walk split: part k = PARTS[k] holds FULL indices [o_k, o_k + PLEN[k]); its core slice is (core.drop d_k).take n_k
idx = [c_ - 1 for c_ in core]   # 0-based FULL indices of the core, increasing
off = [sum(PLEN[:k]) for k in range(len(PARTS) + 1)]
import bisect
dpos = [bisect.bisect_left(idx, o_) for o_ in off]
open(os.path.join(pd, 'Core.lean'), 'w').write("module\n\n%s\n%snamespace %s\ndef core : List (Nat × List Nat) := %s\nend %s\n"
    % (''.join('import all CoverCert.%s.%s\n' % (mod, p_) for p_ in parts), HDR, NS, P, NS))
WG = int(os.environ.get('WALK_GROUP', '6000')); groups = [[]]; acc = 0
for k in range(len(PARTS)):
    if groups[-1] and acc + PLEN[k] > WG: groups.append([]); acc = 0
    groups[-1].append(k); acc += PLEN[k]
last = len(PARTS) - 1
for g, ks in enumerate(groups):
    th = []
    for k in ks:
        sl = 'core.drop %d' % dpos[k] if k == last else '(core.drop %d).take %d' % (dpos[k], dpos[k + 1] - dpos[k])
        th.append("theorem wk%d : walkN (%s) %d (%s) = true := by decide +kernel" % (k, PARTS[k], off[k], sl))
        th.append("theorem lk%d : %d + (%s).length = %d := by decide +kernel" % (k, off[k], PARTS[k], off[k + 1]))
    open(os.path.join(pd, 'K%d.lean' % g), 'w').write(
        "module\n\nimport TabAll\nimport CoverDefs\nimport Split\nimport Walk\nimport all CoverCert.%s.Core\n\n%snamespace %s\n%s Dim8Lift.Walk\n%s\nend %s\n"
        % (mod, HDR, NS, OPEN, '\n'.join(th), NS))
chain = 'wk%d' % last
for k in range(last - 1, -1, -1):
    chain = 'walkN_step _ _ %d %d core %d %d lk%d wk%d (%s)' % (off[k], off[k + 1], dpos[k], dpos[k + 1] - dpos[k], k, k, chain)
RN = '(%s)' % PARTS[-1]   # right-nested (`++` is left-associative): P0 ++ (P1 ++ (... ++ Pm)), as walkN_step chains
for p_ in reversed(PARTS[:-1]): RN = '(%s) ++ (%s)' % (p_, RN)
WALK = ("theorem walk_ok : walkN (%s) 0 core = true := by\n"
        "  have e : %s = %s := by simp only [%s]\n"
        "  have h : walkN (%s) 0 (core.drop 0) = true := %s\n"
        "  rw [List.drop_zero] at h; rw [e]; exact h\n"
        % (FULL, FULL, RN, SIMP, RN, chain))
stats['walk'] = dict(parts=len(PARTS), groups=len(groups))
open(os.path.join(gen, 'Cover' + mod + '.lean'), 'w').write(
    "module\n\npublic import CoverDefs\npublic import TabAll\n%simport RenN\nimport Walk\nimport WalkSplit\n%s"
    "import all CoverCert.%s.Core\n%s"
    "import all LocalWindowUnsat.%s\nimport all LocalWindowCnf.%s\n\n%snamespace %s\n%s Dim8Lift.RenN Dim8Lift.Walk Snake9.LocalWindow\n"
    "%s"
    "theorem ren_ok : renN tree.get %s.raw (core.map Prod.snd) = true := by\n  simp only [%s.raw, core, List.map_append]\n  exact %s\n"
    "/-- the certificate -/\npublic theorem unsat : Unsat (%s) := by\n"
    "  have h := unsat_of_renN tree.get _ _ ren_ok %s.unsat\n  rw [List.map_map] at h\n  exact unsat_of_walkN _ core walk_ok h\nend %s\n"
    "#print axioms %s.unsat\n"
    % ('public import Split\n' if US else '', ''.join('import all CoverCert.%s.%s\n' % (mod, p) for p in parts), mod,
       ''.join('import all CoverCert.%s.K%d\n' % (mod, g) for g in range(len(groups))), mod, mod, HDR, NS, OPEN, WALK,
       LW, LW, ren, FULL, LW, NS, NS))
# module form of the pilot.py / genv3stream outputs (as in make_cert.py)
def modz(path, priv=(), allimp=()):
    ls = open(path).read().split('\n'); i = 0
    while i < len(ls) and (ls[i].startswith('import ') or not ls[i].strip()): i += 1
    open(path, 'w').write('\n'.join(['module', ''] + ['import ' + x for x in priv] + ['import all ' + x for x in allimp])
                          + '\n\nset_option maxHeartbeats 0   -- long clauses: data chunks exceed the default\n' + '\n'.join(ls[i:]))
cw = os.path.join(gen, 'LocalWindowCnf', mod)
for r_ in rparts: modz(os.path.join(cw, r_ + '.lean'))
modz(cw + '.lean', priv=['LocalWindowModel'], allimp=['LocalWindowCnf.%s.%s' % (mod, r_) for r_ in rparts])
modz(os.path.join(gen, 'LocalWindowUnsat', mod + '.lean'), priv=['LratV3', 'ProofPack'], allimp=['LocalWindowCnf.' + mod])
open(os.path.join(gen, mod + '.modules'), 'w').write(' '.join(
    ['LocalWindowCnf/%s/%s' % (mod, p) for p in rparts] + ['LocalWindowCnf/' + mod, 'LocalWindowUnsat/' + mod, 'CoverCert/%s/Tree' % mod]
    + ['CoverCert/%s/%s' % (mod, p) for p in parts] + ['CoverCert/%s/Core' % mod]
    + ['CoverCert/%s/K%d' % (mod, g) for g in range(len(groups))] + ['Cover' + mod]))
stats['gen_s'] = round(time.time() - t0, 1)
print(json.dumps(stats))
