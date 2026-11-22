#!/usr/bin/env python3
"""Final assembly and audit of a(9) <= 229 from the milestone-39 certificates.

    assemble_d8.py collect --work DIR [--prefix refs/heads/xfer/d8]   fetch every published ref by name, check hashes
    assemble_d8.py status  --work DIR                                  what is present / missing
    assemble_d8.py final   --work DIR --stack DIR [--jobs N]           build Final229 and audit it

    assemble_d8.py final   --work DIR --stack DIR --glue-test       the same with every certificate as a hypothesis
                           [--skip-checks]                          ... and the table checks t5_ok / t6_ok too (fast)

Assembly machine (once): bash scripts/make_tables.sh (tables, lean/gen); python3 cert/prod_d8.py setup --stack DIR.

collect: `git ls-remote origin '<prefix>/*'` (the cube workers w*, the tail workers t*, any cover ref), then each ref
fetched by name into WORK/idx (a private git directory; no unscoped fetch, nothing written to the checkout's refs).
Each ref holds manifest.jsonl and <Module>.olean files (public .olean only). A certificate is accepted
when its manifest line has status OK and the sha256 of the .olean matches. Accepted files go to WORK/olean,
their manifest lines to WORK/accepted.jsonl.
Expected certificates: CubeQ<A> for every (k, A) of the 2,161 representatives (data/q6_29.txt; prod_d8.py, or
tail_d8.py for the TOO_BIG and k = 31/32 cubes: same module name and interface `Snake9.CubeProv.Q<A>.unsat`),
CoverKC5 (`Snake9.CoverCert.KC5.unsat`) and CoverKC6R<r5> (`Snake9.CoverCert.KC6R<r5>.unsat`) for the 35 Q5
representatives.
Stack consistency: every accepted certificate records the commit it was built at. The kernel checked it there;
what must not differ is the meaning of its statement, i.e. the sources of its public closure: for a cube the
import closure of CubeCnf, for a cover that of CoverDefs plus the table generators (TabAll is generated), and
in both cases work/final_lean, lean435/tools/port.py and cert/port39.py. They must equal those of the
assembling commit (`git diff --quiet`), otherwise the certificate is rejected. (Comparing all of lean/ would
reject every certificate built before ea5ecf379, which only changed Split.lean, a private import.)

final:
  1. the table checks (lean/gen/T5c*Ok, T6c*Ok and their parts, ported to modules) are built against the
     stack, at most --jobs at a time under a memory cap (a check can take 10 GB);
  2. Final229.lean (module) is generated: it imports the tables, the checks and the 2,197 certificate
     interfaces, and proves `public theorem upper_229 : ∀ {m : Nat}, Snake9.Snake m → m ≤ 229` from
     `Dim8Lift.upper_of_certsQ`; it is compiled with `lean --setup` whose importArts list only public
     .olean files (certificate data is never loaded);
  3. Audit229.lean is compiled from a clean directory that holds only the public .olean files of the
     stack and Final229 (as lean435/tools/audit.py): `#check` and `#print axioms` must show
     [propext, Classical.choice, Quot.sound] and the statement over the audited `Snake9.Snake`.
"""
import argparse, concurrent.futures, hashlib, json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__)); M = os.path.abspath(os.path.join(HERE, '..'))
ROOT = os.path.abspath(os.path.join(M, '..', '..')); LEAN = '/opt/lean-4.35.0-linux/bin/lean'
COMMON_INPUTS = ['work/final_lean', 'lean435/tools/port.py', 'milestones/39-dim8-lift/cert/port39.py']
TABLE_GEN = ['scripts/enumk_raw.c', 'scripts/enum6_raw.c', 'scripts/gentables.py', 'scripts/genlean_tables.py', 'data/q5_15.txt']
Q5REPS = None


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def reps():
    out = []
    for l in open(os.path.join(M, 'data', 'q6_29.txt')):
        k, _, h = l.split(); out.append((int(k), h))
    return out


def q5reps():
    global Q5REPS
    if Q5REPS is None:
        r = sh([LEAN, '--run', 'CovExport.lean', 'list5'], cwd=os.path.join(M, 'lean'),
               env=dict(os.environ, LEAN_PATH=os.path.join(M, 'lean', 'build')))
        assert r.returncode == 0, r.stderr
        Q5REPS = [int(x) for x in r.stdout.split()]
        assert len(Q5REPS) == 35
    return Q5REPS


def expected():
    e = {'CubeQ' + h.upper(): ('cube', k, h) for k, h in reps()}
    e['CoverKC5'] = ('c5', None, None)
    for r in q5reps(): e['CoverKC6R%d' % r] = ('c6', r, None)
    return e


def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def closure(roots):
    """source files (repo paths) of the import closure of roots in milestones/39-dim8-lift/lean (at HEAD)"""
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop(); p = os.path.join(M, 'lean', m + '.lean')
        if m in seen or not os.path.exists(p): continue   # LocalWindowModel, Std: COMMON_INPUTS / Lean
        seen.add(m)
        for l in open(p):
            t = l.split()
            if t[:1] == ['import'] or t[:2] == ['public', 'import']: todo.append(t[-1])
    return ['milestones/39-dim8-lift/lean/%s.lean' % m for m in sorted(seen)]


def inputs(kind):
    if kind == 'cube': return closure(['CubeCnf']) + COMMON_INPUTS
    return closure(['CoverDefs', 'TabDefs']) + ['milestones/39-dim8-lift/' + f for f in TABLE_GEN] + COMMON_INPUTS


def stack_ok(commit, kind, cache={}):
    if (commit, kind) not in cache:
        if sh(['git', 'cat-file', '-e', commit + '^{commit}'], cwd=ROOT).returncode != 0:
            sh(['git', 'fetch', '-q', 'origin', 'research/unconditional-241'], cwd=ROOT)
        cache[commit, kind] = sh(['git', 'diff', '--quiet', commit, 'HEAD', '--'] + inputs(kind), cwd=ROOT).returncode == 0
    return cache[commit, kind]


def collect(a):
    w = os.path.abspath(a.work); od = os.path.join(w, 'olean'); os.makedirs(od, exist_ok=True)
    g = os.path.join(w, 'idx')
    if not os.path.exists(os.path.join(g, '.git')):
        os.makedirs(g, exist_ok=True); sh(['git', 'init', '-q'], cwd=g)
        sh(['git', 'remote', 'add', 'origin', sh(['git', 'remote', 'get-url', 'origin'], cwd=ROOT).stdout.strip()], cwd=g)
    r = sh(['git', 'ls-remote', 'origin', a.prefix + '/*'], cwd=g); assert r.returncode == 0, r.stderr
    refs = [l.split()[1] for l in r.stdout.splitlines() if l.strip()]
    print('%d refs under %s' % (len(refs), a.prefix), flush=True)
    exp = expected(); acc = {}; rej = []
    accf = os.path.join(w, 'accepted.jsonl')
    if os.path.exists(accf):
        for l in open(accf):
            r = json.loads(l); acc[r['module']] = r
    for ref in refs:
        loc = 'refs/d8/' + ref.rsplit('/', 1)[1]
        if sh(['git', 'fetch', '-q', 'origin', '+%s:%s' % (ref, loc)], cwd=g).returncode != 0:
            print('fetch failed', ref); continue
        tip = sh(['git', 'rev-parse', loc], cwd=g).stdout.strip()
        man = sh(['git', 'show', tip + ':manifest.jsonl'], cwd=g).stdout
        for l in man.splitlines():
            r = json.loads(l); m = r['module']
            if r.get('status') != 'OK' or m not in exp or m in acc: continue
            blob = subprocess.run(['git', 'show', '%s:%s.olean' % (tip, m)], cwd=g, capture_output=True).stdout
            if hashlib.sha256(blob).hexdigest() != r.get('sha256'):
                rej.append((m, ref, 'sha256 mismatch')); continue
            if not stack_ok(r.get('commit', ''), 'cube' if m.startswith('CubeQ') else 'cover'):
                rej.append((m, ref, 'stack inputs differ at %s' % r.get('commit'))); continue
            open(os.path.join(od, m + '.olean'), 'wb').write(blob)
            r['ref'] = ref; acc[m] = r
    open(accf, 'w').write(''.join(json.dumps(acc[m]) + '\n' for m in sorted(acc)))
    for x in rej: print('REJECTED', *x)
    print('accepted %d of %d expected certificates' % (len(acc), len(exp)))


def status(a):
    w = os.path.abspath(a.work); exp = expected()
    acc = {json.loads(l)['module'] for l in open(os.path.join(w, 'accepted.jsonl'))} if os.path.exists(os.path.join(w, 'accepted.jsonl')) else set()
    miss = [m for m in exp if m not in acc]
    kinds = {}
    for m in miss: kinds.setdefault(exp[m][0] + ('%d' % exp[m][1] if exp[m][0] == 'cube' else ''), []).append(m)
    print('present %d / %d' % (len(exp) - len(miss), len(exp)))
    for k in sorted(kinds): print('missing %-8s %d%s' % (k, len(kinds[k]), (': ' + ' '.join(kinds[k][:8])) if len(kinds[k]) <= 40 else ''))
    return miss


def gen_final(w, exp, test=False, present=(), skip_checks=False):
    """Final229.lean: all premises of upper_of_certsQ at L = 116, from the certificate interfaces.
    test: GlueTest229.lean, the same glue with the certificates as hypotheses (the present cube certificates
    are imported and checked against their statements in chunk lemmas b<i>); proves `upper_229_of`."""
    rp = reps(); q5 = q5reps(); CH = 100
    chunks = [rp[i:i + CH] for i in range(0, len(rp), CH)]
    checks = open(os.path.join(M, 'lean', 'gen', 'checks.txt')).read().split()
    top = [c for c in checks if re.fullmatch(r'T[56]c\d+Ok', c)]
    n5 = sum(1 for c in top if c.startswith('T5')); n6 = sum(1 for c in top if c.startswith('T6'))
    # the glue test's public statement names the tables: their modules must be imported publicly
    pi = 'public import ' if test else 'import '
    L = ['module', '', 'public import Snake9'] + [pi + m for m in ('Final', 'TabAll', 'Reps', 'CoverDefs')]
    L += ['import ' + c for c in top if not skip_checks]
    L += [pi + 'Q5Reps'] + ['import T5c%dQ' % i for i in range(n5)]
    L += ['import ' + m for m in sorted(exp) if not test or m in present]
    L += ['', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
          '/-! a(9) <= 229 (milestone 39): every premise of `Dim8Lift.upper_of_certsQ` at L = 116 from a',
          'kernel-checked certificate. Generated by milestones/39-dim8-lift/cert/assemble_d8.py. -/',
          'namespace Dim8Lift.Final229', 'open Dim8Lift Dim8Lift.Tab Dim8Lift.Cube Snake9.LocalWindow', '',
          'def AllP {α : Type} (P : α → Prop) : List α → Prop', '  | [] => True', '  | x :: xs => P x ∧ AllP P xs', '',
          'theorem allP_append {α : Type} (P : α → Prop) : ∀ (a b : List α), AllP P a → AllP P b → AllP P (a ++ b)',
          '  | [], _, _, hb => hb', '  | _ :: as, b, ⟨h, ha⟩, hb => ⟨h, allP_append P as b ha hb⟩', '',
          'theorem allP_mem {α : Type} (P : α → Prop) : ∀ (l : List α), AllP P l → ∀ x ∈ l, P x',
          '  | [], _, x, hx => by simp at hx',
          '  | y :: ys, ⟨h, hs⟩, x, hx => by',
          '    rcases List.mem_cons.mp hx with rfl | hx',
          '    · exact h', '    · exact allP_mem P ys hs x hx', '',
          'abbrev PC (r : Nat × Nat) : Prop := Unsat (cubeCnfQ 13 116 r.2 r.1)', '']
    for i, ch in enumerate(chunks):
        L.append('def R%d : List (Nat × Nat) := [%s]' % (i, ', '.join('(%d, %d)' % (k, int(h, 16)) for k, h in ch)))
        if not test:
            L.append('theorem a%d : AllP PC R%d := ⟨%s, trivial⟩' % (i, i, ', '.join('Snake9.CubeProv.Q%s.unsat' % h.upper() for _, h in ch)))
    if test:
        pr = [x for x in rp if 'CubeQ' + x[1].upper() in present]
        for i in range(0, len(pr), CH):
            ch = pr[i:i + CH]
            L.append('def P%d : List (Nat × Nat) := [%s]' % (i // CH, ', '.join('(%d, %d)' % (k, int(h, 16)) for k, h in ch)))
            L.append('theorem b%d : AllP PC P%d := ⟨%s, trivial⟩' % (i // CH, i // CH, ', '.join('Snake9.CubeProv.Q%s.unsat' % h.upper() for _, h in ch)))
    cat = ' ++ '.join('R%d' % i for i in range(len(chunks)))
    app = 'a0'   # `++` is left-associative: R0 ++ R1 ++ R2 = (R0 ++ R1) ++ R2
    for i in range(1, len(chunks)): app = 'allP_append PC _ _ (%s) a%d' % (app, i)
    L += ['theorem reps_eq : reps = %s := by decide' % cat]
    if test: L += ['theorem hcubes_of (h : AllP PC (%s)) : ∀ r ∈ reps, Unsat (cubeCnfQ 13 116 r.2 r.1) := by' % cat,
                   '  rw [reps_eq]', '  exact allP_mem PC _ h', '']
    else: L += ['theorem hcubes : ∀ r ∈ reps, Unsat (cubeCnfQ 13 116 r.2 r.1) := by',
                '  rw [reps_eq]', '  exact allP_mem PC _ (%s)' % app, '']
    if not skip_checks: L += [
          'theorem t5_ok : t5.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true := by',
          '  simp only [t5, List.all_append, %s, Bool.and_self]' % ', '.join('t5c%d_ok' % i for i in range(n5)),
          'theorem t6_ok : t6.all (fun e => chk 6 e.2.1 e.2.2.1 e.2.2.2 && reps.contains (pcN 64 e.2.2.2, e.2.2.2)) = true := by',
          '  simp only [t6, List.all_append, %s, Bool.and_self]' % ', '.join('t6c%d_ok' % i for i in range(n6)), '']
    # t5_reps per table chunk (T5c<i>Q, built with the checks): one kernel evaluation of the whole t5 needs > 13 GB
    L += ['theorem t5_reps : t5.all (fun e => Q5.contains e.2.2) = true := by',
          '  simp only [t5, List.all_append, %s, Bool.and_self]' % ', '.join('t5c%d_reps' % i for i in range(n5)),
          'abbrev PV (r : Nat) : Prop := Unsat (c6Cnf r ((t6.filter (·.1 == r)).map (·.2.1)))',
          'theorem hU6_of (covers : AllP PV Q5) : ∀ e ∈ t5, Unsat (c6Cnf e.2.2 ((t6.filter (·.1 == e.2.2)).map (·.2.1))) := by',
          '  intro e he',
          '  have h := List.all_eq_true.mp t5_reps e he',
          '  exact allP_mem PV Q5 covers e.2.2 (by simpa using h)']
    if test:   # the certificate statements as hypotheses, in public form (no private AllP / PV in a public statement)
        H = ((' (t5_ok : t5.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true)'
              ' (t6_ok : t6.all (fun e => chk 6 e.2.1 e.2.2.1 e.2.2.2 && reps.contains (pcN 64 e.2.2.2, e.2.2.2)) = true)\n   ')
             if skip_checks else '') + (' (hU5 : Unsat (c5Cnf (t5.map (·.1))))'
             ' (covers : ∀ r ∈ Q5, Unsat (c6Cnf r ((t6.filter (·.1 == r)).map (·.2.1))))\n    (hcs : ∀ r ∈ reps, Unsat (cubeCnfQ 13 116 r.2 r.1))')
        args = ('t5_ok t6_ok ' if skip_checks else '') + 'hU5 covers hcs'
        L += ['', 'theorem upper_229_priv%s : ∀ {m : Nat}, Snake9.Snake m → m ≤ 229 :=' % H,
              '  upper_of_certsQ (L := 116) (by decide) (by decide) t5 t6 reps t5_ok t6_ok hU5',
              '    (fun e he => covers e.2.2 (by simpa using List.all_eq_true.mp t5_reps e he)) hcs',
              '/-- glue test: a(9) ≤ 229 from the certificate statements, taken as hypotheses -/',
              'public theorem upper_229_of%s : ∀ {m : Nat}, Snake9.Snake m → m ≤ 229 :=' % H,
              '  upper_229_priv ' + args, '',
              'end Dim8Lift.Final229', '', '#print axioms Dim8Lift.Final229.upper_229_of', '']
    else:
        L += ['theorem hU5 : Unsat (c5Cnf (t5.map (·.1))) := Snake9.CoverCert.KC5.unsat',
              'theorem covers : AllP PV Q5 := ⟨%s, trivial⟩' % ', '.join('Snake9.CoverCert.KC6R%d.unsat' % r for r in q5),
              '', 'theorem upper_229_priv : ∀ {m : Nat}, Snake9.Snake m → m ≤ 229 :=',
              '  upper_of_certsQ (L := 116) (by decide) (by decide) t5 t6 reps t5_ok t6_ok hU5 (hU6_of covers) hcubes',
              '/-- a(9) ≤ 229: every snake (induced path) in Q9 has at most 229 edges. -/',
              'public theorem upper_229 : ∀ {m : Nat}, Snake9.Snake m → m ≤ 229 := upper_229_priv', '',
              'end Dim8Lift.Final229', '', '#print axioms Dim8Lift.Final229.upper_229', '']
    p = os.path.join(w, 'test' if test else 'final', 'GlueTest229.lean' if test else 'Final229.lean'); os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w').write('\n'.join(L)); return p


def public_arts(stack, extra_dirs, mods):
    """importArts for `lean --setup`: the transitive public closure of mods, public .olean files only."""
    b = os.path.join(stack, 'build'); arts = {}; todo = list(mods)
    while todo:
        m = todo.pop()
        if m in arts or m in ('Std', 'Init', 'Lean'): continue
        o = None
        for d in extra_dirs + [b]:
            if os.path.exists(os.path.join(d, m.replace('.', '/') + '.olean')): o = os.path.join(d, m.replace('.', '/') + '.olean'); break
        assert o, 'no public .olean for ' + m
        arts[m] = [[o], []]
        src = os.path.join(stack, m.replace('.', '/') + '.lean')
        # certificate interfaces (no source in the stack): their public imports, as make_cert.py,
        # make_split.py and make_cover_cert.py write them
        if m.startswith('CubeQ'): todo.append('CubeCnf')
        if m.startswith('CoverKC'): todo += ['CoverDefs', 'TabAll']
        if os.path.exists(src):
            for l in open(src):
                if l.startswith('public import '): todo.append(l.split()[2])
    return arts


def final(a):
    w = os.path.abspath(a.work); st = os.path.abspath(a.stack)
    miss = status(a)
    if miss and not a.allow_missing and not a.glue_test: sys.exit('missing certificates: not assembling')
    exp = expected(); present = set(exp) - set(miss)
    # 1. table checks, ported and built in the stack (memory-capped parallel builds)
    skip = a.glue_test and a.skip_checks
    # gen/checks.txt also names gen/Final229.lean, genlean_checks.py's older (non-module) assembly: not used here
    checks = [c for c in open(os.path.join(M, 'lean', 'gen', 'checks.txt')).read().split() if re.fullmatch(r'T[56]c\d+(P\d+)?Ok', c)]
    r = sh([sys.executable, os.path.join(HERE, 'port39.py'), st, 'Final', 'TabAll', 'Reps', 'CoverDefs'] + checks); assert r.returncode == 0, r.stderr
    order = r.stdout.split()
    def build(m):
        o = os.path.join(st, 'build', m + '.olean')
        if os.path.exists(o): return m, 0, 0
        t = time.time()
        rr = sh([LEAN, '--root=.', '-o', o, m + '.lean'], cwd=st, env=dict(os.environ, LEAN_PATH=os.path.join(st, 'build')))
        return m, rr.returncode, round(time.time() - t)
    # Q5Reps (the 35 Q5 representatives) and T5c<i>Q (`t5c<i>.all (fun e => Q5.contains e.2.2) = true`, ~2 GB each)
    n5 = sum(1 for c in checks if re.fullmatch(r'T5c\d+Ok', c))
    open(os.path.join(st, 'Q5Reps.lean'), 'w').write(
        'module\n\npublic import TabAll\n\n@[expose] public section\n\nnamespace Dim8Lift.Final229\n'
        '/-- the 35 Q5 representatives (CovExport.lean list5) -/\ndef Q5 : List Nat := [%s]\nend Dim8Lift.Final229\n'
        % ', '.join(map(str, q5reps())))
    for i in range(n5):
        open(os.path.join(st, 'T5c%dQ.lean' % i), 'w').write(
            'module\n\npublic import Q5Reps\n\n@[expose] public section\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
            'namespace Dim8Lift.Final229\nopen Dim8Lift.Tab\n'
            'theorem t5c%d_reps : t5c%d.all (fun e => Q5.contains e.2.2) = true := by decide +kernel\nend Dim8Lift.Final229\n' % (i, i))
    order += ['Q5Reps']; qs = ['T5c%dQ' % i for i in range(n5)]
    data = [m for m in order if not m.endswith('Ok')]; chk = [m for m in order if m.endswith('Ok')]
    for m in data:
        res = build(m); assert res[1] == 0, res
    parts = [m for m in chk if 'P' in m[3:]]; tops = [m for m in chk if m not in parts]
    # most checks take 2-2.5 GB, some T6 parts much more (two at once were OOM-killed in a 13 GB session):
    # a check that fails in the parallel pass is retried alone
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        for grp in ((parts, tops, qs) if not skip else (qs,)):
            bad = []
            for m, rc, s in ex.map(build, grp):
                print('check %s rc=%d %ds' % (m, rc, s), flush=True)
                if rc != 0: bad.append(m)
            for m in bad:
                m, rc, s = build(m); print('check %s rc=%d %ds (alone)' % (m, rc, s), flush=True); assert rc == 0, m
    # 2. Final229 against public .olean files only
    p = gen_final(w, exp, a.glue_test, present, skip); fd = os.path.dirname(p); nm = os.path.basename(p)[:-5]
    imps = [l.split()[-1] for l in open(p) if l.startswith(('import ', 'public import '))]
    arts = public_arts(st, [os.path.join(w, 'olean')], imps)
    json.dump(dict(name=nm, isModule=True, importArts=arts, dynlibs=[], plugins=[], options={}), open(os.path.join(fd, 'setup.json'), 'w'))
    t = time.time()
    r = sh([LEAN, '--setup', 'setup.json', '-o', nm + '.olean', nm + '.lean'], cwd=fd, env=dict(os.environ, LEAN_PATH='/nonexistent'))
    out = r.stdout + r.stderr
    print('%s: rc=%d %ds' % (nm, r.returncode, time.time() - t)); print(out[-3000:])
    assert r.returncode == 0
    if a.glue_test:
        ok = 'depends on axioms: [propext, Classical.choice, Quot.sound]' in out and 'sorry' not in out and 'error' not in out
        print('GLUE TEST', 'PASSED' if ok else 'FAILED', '(%d present cube certificates checked against their statements)'
              % sum(1 for m in present if m.startswith('CubeQ')))
        sys.exit(0 if ok else 1)
    # 3. audit from a clean directory: the public .olean of Final229 and the closure of its public imports
    ad = os.path.join(w, 'audit'); shutil.rmtree(ad, ignore_errors=True); os.makedirs(ad)
    shutil.copyfile(os.path.join(fd, 'Final229.olean'), os.path.join(ad, 'Final229.olean'))
    arts = public_arts(st, [ad], ['Snake9']); arts['Final229'] = [[os.path.join(ad, 'Final229.olean')], []]
    open(os.path.join(ad, 'Audit229.lean'), 'w').write(
        'module\n\nimport Final229\n\n#check @Dim8Lift.Final229.upper_229\n#print Snake9.Snake\n#print Snake9.Adj\n'
        '#print axioms Dim8Lift.Final229.upper_229\n')
    json.dump(dict(name='Audit229', isModule=True, importArts=arts, dynlibs=[], plugins=[], options={}), open(os.path.join(ad, 'setup.json'), 'w'))
    r = sh([LEAN, '--setup', 'setup.json', 'Audit229.lean'], cwd=ad, env=dict(os.environ, LEAN_PATH='/nonexistent'))
    out = r.stdout + r.stderr; open(os.path.join(w, 'audit229.txt'), 'w').write(out); print(out)
    ok = (r.returncode == 0 and 'depends on axioms: [propext, Classical.choice, Quot.sound]' in out
          and '∀ {m : Nat}, Snake9.Snake m → m ≤ 229' in out and 'sorry' not in out)
    print('AUDIT', 'PASSED' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); sp = ap.add_subparsers(dest='cmd', required=True)
    c = sp.add_parser('collect'); c.add_argument('--work', required=True); c.add_argument('--prefix', default='refs/heads/xfer/d8')
    s = sp.add_parser('status'); s.add_argument('--work', required=True)
    f = sp.add_parser('final'); f.add_argument('--work', required=True); f.add_argument('--stack', required=True)
    f.add_argument('--jobs', type=int, default=1); f.add_argument('--allow-missing', action='store_true')
    f.add_argument('--glue-test', action='store_true'); f.add_argument('--skip-checks', action='store_true')
    a = ap.parse_args()
    {'collect': collect, 'status': status, 'final': final}[a.cmd](a)
