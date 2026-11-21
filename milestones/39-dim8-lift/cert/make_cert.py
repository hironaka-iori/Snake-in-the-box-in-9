"""One complete cube certificate: Unsat (cubeCnfQ 13 L A k) as Lean modules.
usage: python3 make_cert.py L Ahex k outroot   (needs milestones/39-dim8-lift/lean/build; writes outroot/...)
Steps: Lean export of cubeCnfQ, cadical --lrat, core compaction (pilot.py), v3 replay (genv3stream),
provenance data (tags from ExportTags) in parts, and the glue module Cube<Ahex>.lean with
  theorem unsat : Unsat (cubeCnfQ 13 L A k)."""
import sys, os, subprocess, json, time
L, Ahex, k, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
HERE = os.path.dirname(os.path.abspath(__file__)); M = os.path.join(HERE, '..'); LEANDIR = os.path.join(M, 'lean')
ROOT = os.path.abspath(os.path.join(M, '..', '..')); LEAN = '/opt/lean-4.35.0-linux/bin/lean'
mod = 'Q' + Ahex.upper(); W = os.path.join(out, 'work', mod); os.makedirs(W, exist_ok=True)
env = dict(os.environ, LEAN_PATH=os.path.join(LEANDIR, 'build'))
t0 = time.time(); stats = dict(module=mod, L=L, A=Ahex, k=k)
cnf = os.path.join(W, 'f.cnf'); tags = os.path.join(W, 'tags.txt'); lrat = os.path.join(W, 'f.lrat')
subprocess.run([LEAN, '--run', 'Export.lean', '13', str(L), Ahex, str(k), cnf, 'q'], cwd=LEANDIR, env=env, check=True)
subprocess.run([LEAN, '--run', 'ExportTags.lean', '13', str(L), Ahex, str(k), tags], cwd=LEANDIR, env=env, check=True)
s = time.time()
# SOLVE_LIMIT (s, from prod_d8.py): a longer solve means a certificate too big for this machine's memory
# (~28-52 k hints per solver second); stop, delete the partial LRAT, exit 11 (recorded as TOO_BIG)
lim = float(os.environ.get('SOLVE_LIMIT', '0'))
try:
    r = subprocess.run(['cadical', '-q', '--lrat', '--binary=false', cnf, lrat], capture_output=True, text=True, timeout=lim or None)
except subprocess.TimeoutExpired:
    for f_ in (lrat, cnf, tags):
        if os.path.exists(f_): os.remove(f_)
    print(json.dumps(dict(stats, status='TOO_BIG', solve_limit=lim))); sys.exit(11)
stats['solve_s'] = round(time.time() - s, 1)
if 's SATISFIABLE' in r.stdout:
    print(json.dumps(dict(stats, status='SATISFIABLE'))); sys.exit(10)   # a SAT cube: report, never certify
assert 's UNSATISFIABLE' in r.stdout, r.stdout[:200]
gen = os.path.join(out, 'gen'); os.makedirs(gen, exist_ok=True)
c = json.loads(subprocess.run(['python3', os.path.join(HERE, 'pilot.py'), cnf, lrat, mod, gen], capture_output=True, text=True, check=True).stdout)
stats.update(core=c)
g = json.loads(subprocess.run(['python3', os.path.join(ROOT, 'lean435', 'tools', 'genv3stream.py'), '--work', gen, '--data', os.path.join(gen, 'core'),
                               '--out', gen, '--off', str(c['vars'] + 1), mod], capture_output=True, text=True, check=True).stdout.strip().splitlines()[-1])
stats['replay'] = {x: g[x] for x in ('lemmas', 'hints', 'segments', 'wbits', 'off', 'lean_bytes')}
os.remove(lrat)
# provenance data, in core order, Nat codes
glue = json.load(open(os.path.join(gen, mod + '.glue.json')))
core = glue['core_ids']; cs = set(core)
tagof = {}
for l in open(tags):
    t, cl = l.split(' | '); tagof.setdefault(tuple(cl.split()), t.split())
enc = lambda l: 2 * abs(l) + (0 if l > 0 else 1)
rows = {}; i = 0
for line in open(cnf):
    if line.startswith('p'): continue
    i += 1
    if i in cs:
        lits = line.split()[:-1]
        rows[i] = '([%s], [%s])' % (', '.join(tagof[tuple(lits)]), ', '.join(str(enc(int(x))) for x in lits))
os.remove(cnf); os.remove(tags)
CH = 4000   # must equal pilot.py's chunk size: P_i is renamed-checked against R_i
rparts = open(os.path.join(gen, 'LocalWindowCnf', mod + '.parts')).read().split()
pd = os.path.join(gen, 'CubeProv', mod); os.makedirs(pd, exist_ok=True)
ordered = [rows[c_] for c_ in core]
parts = ['P%d' % (j // CH) for j in range(0, len(ordered), CH)]
assert len(parts) == len(rparts), (parts, rparts)
# variable renaming as a balanced tree: BT.get t v' = back[v'-1]
back = glue['back']; N = len(back)
SUB = []   # subtrees at depth 7 become their own definitions (one huge nested literal exceeds maxRecDepth)
def tree(i0, step, depth=0):
    if i0 + step > N: return 'BT.lf %d' % (back[i0 - 1] if 1 <= i0 <= N else 0)
    if depth == 7:
        SUB.append('def s%d : BT := %s' % (len(SUB), tree(i0, step, 8 + depth))); return 's%d' % (len(SUB) - 1)
    return 'BT.nd (%s) (%s)' % (tree(i0, 2 * step, depth + 1), tree(i0 + step, 2 * step, depth + 1))
NS = 'Snake9.CubeProv.' + mod; LW = 'Snake9.LocalWindow.' + mod
HDR = "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
open(os.path.join(pd, 'Tree.lean'), 'w').write("import RenN\n%snamespace %s\nopen Dim8Lift.RenN\n%s\nend %s\n" % (HDR, NS, (lambda top: '\n'.join(SUB) + '\ndef tree : BT := ' + top)(tree(0, 1)), NS))
for j, nm in enumerate(parts):
    open(os.path.join(pd, nm + '.lean'), 'w').write(
        "import Prov\nimport CubeProv.%s.Tree\nimport LocalWindowCnf.%s.%s\n%snamespace %s\nopen Dim8Lift.Prov Dim8Lift.RenN\n"
        "def p%d : List (List Nat × List Nat) := [\n%s]\n"
        "theorem p%d_ok : coreOk 13 %d 0x%s %d p%d = true := by decide +kernel\n"
        "theorem n%d : renN tree.get %s.r%d (p%d.map Prod.snd) = true := by decide +kernel\nend %s\n"
        % (mod, mod, rparts[j], HDR, NS, j, ",\n".join(ordered[j * CH:(j + 1) * CH]), j, L, Ahex, k, j, j, LW, j, j, NS))
P = ' ++ '.join('p%d' % j for j in range(len(parts)))
# `++` is left-associative: raw = ((r0 ++ r1) ++ r2) ..., so the chain is built left to right
ren = 'n0'
for j in range(1, len(parts)): ren = 'renN_app _ (%s) n%d' % (ren, j)
open(os.path.join(gen, 'Cube' + mod + '.lean'), 'w').write(
    "import LocalWindowUnsat.%s\n%s%snamespace %s\nopen Dim8Lift.Prov Dim8Lift.RenN Snake9.LocalWindow\n"
    "def core : List (List Nat × List Nat) := %s\n"
    "theorem core_ok : coreOk 13 %d 0x%s %d core = true := by\n  simp only [core, coreOk_append, %s, Bool.and_self]\n"
    "theorem ren_ok : renN tree.get %s.raw (core.map Prod.snd) = true := by\n  simp only [%s.raw, core, List.map_append]\n  exact %s\n"
    "/-- the certificate -/\ntheorem unsat : Unsat (Dim8Lift.Cube.cubeCnfQ 13 %d 0x%s %d) := by\n"
    "  have h := unsat_of_renN tree.get _ _ ren_ok %s.unsat\n  rw [List.map_map] at h\n  exact unsat_of_prov core core_ok h\nend %s\n"
    "#print axioms %s.unsat\n"
    % (mod, ''.join('import CubeProv.%s.%s\n' % (mod, p) for p in parts), HDR, NS, P, L, Ahex, k,
       ', '.join('p%d_ok' % j for j in range(len(parts))), LW, LW, ren, L, Ahex, k, LW, NS, NS))
open(os.path.join(gen, mod + '.modules'), 'w').write(' '.join(
    ['LocalWindowCnf/%s/%s' % (mod, p) for p in rparts] +
    ['LocalWindowCnf/' + mod, 'LocalWindowUnsat/' + mod, 'CubeProv/%s/Tree' % mod] + ['CubeProv/%s/%s' % (mod, p) for p in parts] + ['Cube' + mod]))
# Lean 4.35 module form (the default; NOMOD=1 keeps plain files for the unported stack). All imports are
# private; certificate data is reached by `import all`. Only `unsat` of the top module is public, so its
# public .olean holds just that statement and an importer never loads the certificate data.
def modz(path, priv=(), allimp=(), pub=(), public=None):
    ls = open(path).read().split('\n'); i = 0
    while i < len(ls) and (ls[i].startswith('import ') or not ls[i].strip()): i += 1
    hdr = ['module', ''] + ['public import ' + x for x in pub] + ['import ' + x for x in priv] + ['import all ' + x for x in allimp]
    body = '\n'.join(ls[i:])
    if public: assert body.count(public) == 1; body = body.replace(public, 'public ' + public)
    open(path, 'w').write('\n'.join(hdr) + '\n\n' + body)
if not os.environ.get('NOMOD'):
    cw = os.path.join(gen, 'LocalWindowCnf', mod)
    for r in rparts: modz(os.path.join(cw, r + '.lean'))
    modz(cw + '.lean', priv=['LocalWindowModel'], allimp=['LocalWindowCnf.%s.%s' % (mod, r) for r in rparts])
    modz(os.path.join(gen, 'LocalWindowUnsat', mod + '.lean'), priv=['LratV3', 'ProofPack'], allimp=['LocalWindowCnf.' + mod])
    modz(os.path.join(pd, 'Tree.lean'), priv=['RenN'])
    for j, nm in enumerate(parts):
        modz(os.path.join(pd, nm + '.lean'), priv=['Prov'], allimp=['CubeProv.%s.Tree' % mod, 'LocalWindowCnf.%s.%s' % (mod, rparts[j])])
    modz(os.path.join(gen, 'Cube' + mod + '.lean'), pub=['CubeCnf'], priv=['RenN', 'Prov'],
         allimp=['CubeProv.%s.%s' % (mod, p_) for p_ in parts] + ['LocalWindowUnsat.' + mod, 'LocalWindowCnf.' + mod],
         public='theorem unsat :')
stats['gen_s'] = round(time.time() - t0, 1)
print(json.dumps(stats))
