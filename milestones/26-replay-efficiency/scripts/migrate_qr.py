"""Packed drop-in replacements for the replays of the 237 (`Q*`) and 236 (`R*`) windows.

The old replays `LocalWindowUnsat.<M>` (split layout: `Data<k>`, `Check<g>` and a main module)
cost about 29 bytes of `.olean` per hint.  This driver regenerates each window's LRAT from its
committed core with the original settings (`gen_lean_core.core_lrat`: CaDiCaL portfolio, seeds
1-2, one round for `Q*` and two rounds for `R*`, as `run_direction_replays.py gen`), checks that
the proof has the lemma and hint counts of the old main module, and writes the packed single
module (`gen_lean_lrat.py --fast --split --noncomputable-data --packed`, `--seg 25000 --cp 3
--group 4`, the narrowest word width that fits, as before).  The module keeps the name
`LocalWindowUnsat.<M>` and the theorem `Snake9.LocalWindow.<M>.unsat : Unsat cnf`.

  gen   --stage S --work W M ...   packed source S/src/LocalWindowUnsat/<M>.lean; deletes the
                                   LRAT and CNF files of each window when its source is written
  build --stage S [--drop-src] M ...   `lean -o/-i` into S/lib (LEAN_PATH = S/lib, then the
                                   production lib: the staged module shadows the production one)
  old   --stage S M ...            recompile the old Check<g> modules and main module into
                                   S/oldlib (CPU time of the old kernel checks; nothing written
                                   to production)
  swap  --stage S [--commit] [--keep-src] M ...
                                   without --commit: list what would change and the bytes freed.
                                   With --commit: install the staged .olean/.ilean as the
                                   production LocalWindowUnsat/<M>.olean/.ilean, delete the old
                                   LocalWindowUnsat/<M>/ build directory (Data/Check .olean and
                                   .ilean) and source directory (Check<g>.lean), and replace the
                                   old main source by the packed source (--keep-src) or delete it
  agg   --stage S FILE.lean ...    compile each file twice without changing it, against the
                                   production replays (LEAN_PATH = production lib) and against
                                   the staged ones (S/lib first), into S/agg_old and S/agg_packed;
                                   prints the Lean output and compares the two .olean files

Every `lean` runs under `nice -n 15` with an RSS guard (`measure.run_lean`, --rss-cap-gb, default
2.9 GB; the 10 windows of phase B in ../MIGRATION.md need up to 6.5 GB), starts only
when at least --min-avail-gb of memory is available, and every step stops while the disk has
less than --min-disk-mb free.  One JSON line per window and step goes to S/<step>.jsonl.
See ../MIGRATION.md.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
S10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
DATA = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'data')
FINAL = os.path.join(ROOT, 'work', 'final_lean')
LIB = os.path.join(FINAL, '.lake', 'build', 'lib', 'lean')
sys.path.insert(0, S10)
sys.path.insert(0, HERE)
import gen_lean_core as GC   # noqa: E402
import measure               # noqa: E402

# Q: the 387 windows of the bound 237 (cores in lean_core_direction_r4b, replays with 1 round);
# R: the 361 new windows of the bound 236 (lean_core_direction_r4, 2 rounds,
# milestones/10-window-aggregate/local-task-236-replays.md).
SETS = {'Q': dict(set='r4b', data=os.path.join(DATA, 'lean_core_direction_r4b'), rounds=1),
        'R': dict(set='r4', data=os.path.join(DATA, 'lean_core_direction_r4'), rounds=2)}


def cases():
    out = {}
    for pre, S in SETS.items():
        for name, info in json.load(open(os.path.join(S['data'], '_summary.json')))['per_case'].items():
            if info['module'].startswith(pre):
                out[info['module']] = (name, S)
    return out


def disk_free_mb():
    st = os.statvfs(ROOT)
    return st.f_bavail * st.f_frsize / 2**20


def wait_resources(a):
    while disk_free_mb() < a.min_disk_mb or measure_avail_gb() < a.min_avail_gb:
        print('waiting: disk %.0f MB, memory %.1f GB' % (disk_free_mb(), measure_avail_gb()), flush=True)
        time.sleep(60)


def measure_avail_gb():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 2**20
    return 0.0


def old_info(mod):
    """The old split replay of `mod`: header counts, checker, and every production file."""
    src = os.path.join(FINAL, 'LocalWindowUnsat', mod + '.lean')
    txt = open(src).read()
    m = re.search(r'(\d+) lemmas, (\d+) hints,\s*(\d+) segments', txt)
    ck = re.search(r'open Snake9\.(LratFast2\S*)', txt).group(1)
    files = [src] + [os.path.join(LIB, 'LocalWindowUnsat', mod + e) for e in ('.olean', '.ilean')]
    for d in (os.path.join(FINAL, 'LocalWindowUnsat', mod), os.path.join(LIB, 'LocalWindowUnsat', mod)):
        if os.path.isdir(d):
            files += [os.path.join(d, f) for f in sorted(os.listdir(d))]
    files = [f for f in files if os.path.exists(f)]
    olean = [f for f in files if f.endswith('.olean')]
    return dict(lemmas=int(m.group(1)), hints=int(m.group(2)), segments=int(m.group(3)), checker=ck,
                files=files, bytes=sum(os.path.getsize(f) for f in files),
                olean_bytes=sum(os.path.getsize(f) for f in olean), olean_files=len(olean),
                lib_files=sum(1 for f in files if f.startswith(LIB)))


def log(a, step, rec):
    print(json.dumps(rec), flush=True)
    with open(os.path.join(a.stage, step + '.jsonl'), 'a') as f:
        f.write(json.dumps(rec) + '\n')


class DiskPeak:
    """Peak total size of the files in some directories, sampled every 0.2 s."""
    def __init__(self, dirs):
        self.dirs, self.peak, self.stop = dirs, 0, False
        self.t = threading.Thread(target=self.run, daemon=True)
        self.t.start()

    def size(self):
        n = 0
        for d in self.dirs:
            for dp, _, fs in os.walk(d):
                for f in fs:
                    try:
                        n += os.path.getsize(os.path.join(dp, f))
                    except OSError:
                        pass
        return n

    def run(self):
        while not self.stop:
            self.peak = max(self.peak, self.size())
            time.sleep(0.2)

    def done(self):
        self.stop = True
        self.t.join()
        return max(self.peak, self.size())


def gen(a):
    cs = cases()
    cadical = os.path.join(os.path.dirname(measure.LEAN), 'cadical')
    src = os.path.join(a.stage, 'src')
    os.makedirs(a.work, exist_ok=True)
    for mod in a.modules:
        name, S = cs[mod]
        out = os.path.join(src, 'LocalWindowUnsat', mod + '.lean')
        if os.path.exists(out):
            continue
        if disk_free_mb() < a.min_disk_mb:
            raise SystemExit('stop: disk below %d MB' % a.min_disk_mb)
        old = old_info(mod)
        meta = json.load(open(os.path.join(S['data'], name + '.json')))
        rounds = a.rounds if a.rounds else S['rounds']
        peak = DiskPeak([a.work, os.path.dirname(out)])
        t0 = time.time()
        _, info = GC.core_lrat(name, meta['core_ids'], a.work, cadical, list(range(1, a.seeds + 1)),
                               GC.CADICAL_SETS[S['set']]['certs'], rounds=rounds)
        t_lrat = time.time() - t0
        lrat_bytes = os.path.getsize(os.path.join(a.work, name + '.lrat'))
        same = (info['lemmas'], info['hints']) == (old['lemmas'], old['hints'])
        if not same and not a.allow_different:
            peak.done()
            raise SystemExit('%s: core_lrat gives %d lemmas / %d hints, the old replay %d / %d'
                             % (mod, info['lemmas'], info['hints'], old['lemmas'], old['hints']))
        nv = meta.get('variables', 0)
        off = 2400 if nv < 2400 else 3000 if nv < 3000 else 4000
        t1 = time.time()
        for bits in (13, 14, 15, 16, 17):
            cmd = [sys.executable, os.path.join(S10, 'gen_lean_lrat.py'), '--work', a.work, '--data', S['data'],
                   '--out', src, '--seg', '25000', '--cp', '3', '--group', '4', '--wbits', str(bits),
                   '--off', str(off), '--noncomputable-data', '--fast', '--split', '--packed', name]
            fo, fe = os.path.join(a.work, name + '.gen.out'), os.path.join(a.work, name + '.gen.err')
            with open(fo, 'w') as go, open(fe, 'w') as ge:
                p = subprocess.Popen(cmd, stdout=go, stderr=ge)
                _, status, ru = os.wait4(p.pid, 0)
            so, se = open(fo).read(), open(fe).read()
            os.remove(fo)
            os.remove(fe)
            gen_rss_gb = ru.ru_maxrss / 1e6
            if os.waitstatus_to_exitcode(status) == 0:
                stats = json.loads(so.strip().splitlines()[-1])
                break
            if 'too many slots' not in se and 'assert nslots' not in se:
                peak.done()
                raise SystemExit('generation failed for %s:\n%s' % (name, se[-2000:]))
        else:
            raise SystemExit('%s: too many slots even for the widest words' % name)
        t_gen = time.time() - t1
        for ext in ('.lrat', '.lrat.json', '.core.cnf', '.cnf'):
            p = os.path.join(a.work, name + ext)
            if os.path.exists(p):
                os.remove(p)
        osfx = {2400: '', 3000: 'O3k', 4000: 'O4k'}[off] + (str(bits) if bits != 13 else '')
        checker = 'LratFast2' + ('_' + osfx if osfx else '')
        log(a, 'gen', dict(module=mod, case=name, rounds=rounds, seeds=a.seeds, lemmas=info['lemmas'],
                           hints=info['hints'], same_as_old=same, lrat_sha256=info['lrat_sha256'],
                           lrat_bytes=lrat_bytes, wbits=bits, off=off, checker=checker,
                           old_checker=old['checker'], segments=stats['segments'],
                           checkpoints=stats['checkpoints'], forced=stats['forced_segments'],
                           slots=stats['slots'], src_bytes=os.path.getsize(out),
                           src_sha256=hashlib.sha256(open(out, 'rb').read()).hexdigest(),
                           lrat_s=round(t_lrat, 1), gen_s=round(t_gen, 1), gen_rss_gb=round(gen_rss_gb, 3),
                           peak_disk_bytes=peak.done()))


def compile_one(a, srcroot, outdir, mod, ilean=True, lean_path=None):
    """`lean -o` of `mod` into `outdir`.  LEAN_PATH is `outdir` first, then the production lib,
    unless `lean_path` is given.  Lean resolves a module by the first LEAN_PATH entry that holds
    its root directory (`LocalWindowUnsat/`) or root file, so once `outdir` has a
    `LocalWindowUnsat/` directory every `LocalWindowUnsat.*` import resolves there."""
    rel = mod.replace('.', '/')
    f, o = os.path.join(srcroot, rel + '.lean'), os.path.join(outdir, rel + '.olean')
    os.makedirs(os.path.dirname(o), exist_ok=True)
    env = dict(os.environ, LEAN_PATH=lean_path or (outdir + ':' + LIB))
    wait_resources(a)
    args = ['--root=' + srcroot, '-o', o, *(['-i', o[:-6] + '.ilean'] if ilean else []), f]
    st, txt, ru, wall, killed = measure.run_lean(args, env)
    rec = dict(module=mod, ok=st == 0 and not killed, cpu=round(ru.ru_utime + ru.ru_stime, 2), wall=round(wall, 2),
               rss_gb=round(ru.ru_maxrss / 1e6, 3))
    if rec['ok']:
        rec['olean'] = os.path.getsize(o)
        if ilean:
            rec['ilean'] = os.path.getsize(o[:-6] + '.ilean')
    else:
        rec['error'] = txt[-1500:]
    return rec


def axioms(outdir, thm):
    env = dict(os.environ, LEAN_PATH=outdir + ':' + LIB)
    mod = 'LocalWindowUnsat.' + thm.split('.')[2]
    p = os.path.join(outdir, '_axioms.lean')
    with open(p, 'w') as g:
        g.write('import %s\n#print axioms %s\n' % (mod, thm))
    st, txt, _, _, _ = measure.run_lean([p], env)
    os.remove(p)
    m = re.search(r"depends on axioms: \[(.*?)\]", txt, re.S)
    return [x.strip() for x in m.group(1).split(',')] if m else txt.strip()[-500:]


def build(a):
    src, lib = os.path.join(a.stage, 'src'), os.path.join(a.stage, 'lib')
    if not os.path.exists(os.path.join(lib, 'ProofPack.olean')):
        rec = compile_one(a, FINAL, lib, 'ProofPack')
        log(a, 'build', rec)
        if not rec['ok']:
            raise SystemExit('ProofPack failed')
    for mod in a.modules:
        m = 'LocalWindowUnsat.' + mod
        f = os.path.join(src, 'LocalWindowUnsat', mod + '.lean')
        if not os.path.exists(f):
            continue
        rec = compile_one(a, src, lib, m)
        rec['src_bytes'] = os.path.getsize(f)
        if rec['ok'] and a.axioms:
            rec['axioms'] = axioms(lib, 'Snake9.LocalWindow.%s.unsat' % mod)
        log(a, 'build', rec)
        if not rec['ok']:
            raise SystemExit('build failed: ' + mod)
        if a.drop_src:
            os.remove(f)


def old(a):
    """CPU time of the old kernel checks: recompile Check<g> and the main module into S/oldlib
    against the production Data .olean files (their sources were deleted after the build).
    LEAN_PATH is the production lib alone (see `compile_one`); the main module imports the
    production Check .olean files."""
    lib = os.path.join(a.stage, 'oldlib')
    for mod in a.modules:
        d = os.path.join(FINAL, 'LocalWindowUnsat', mod)
        checks = sorted((f[:-5] for f in os.listdir(d) if re.match(r'Check\d+\.lean$', f)), key=lambda s: int(s[5:]))
        recs = []
        for c in checks:
            rec = compile_one(a, FINAL, lib, 'LocalWindowUnsat.%s.%s' % (mod, c), ilean=False, lean_path=LIB)
            recs.append(rec)
            if not rec['ok']:
                raise SystemExit('old check failed: %s %s %s' % (mod, c, rec.get('error')))
        rec = compile_one(a, FINAL, lib, 'LocalWindowUnsat.' + mod, ilean=False, lean_path=LIB)
        recs.append(rec)
        o = old_info(mod)
        log(a, 'old', dict(module=mod, hints=o['hints'], lemmas=o['lemmas'], segments=o['segments'],
                           checker=o['checker'], check_modules=len(checks),
                           check_cpu=round(sum(r['cpu'] for r in recs[:-1]), 2), main_cpu=recs[-1]['cpu'],
                           max_rss_gb=max(r['rss_gb'] for r in recs), old_bytes=o['bytes'],
                           old_olean_bytes=o['olean_bytes'], old_olean_files=o['olean_files'],
                           old_files=len(o['files']), ok=all(r['ok'] for r in recs)))
        shutil.rmtree(os.path.join(lib, 'LocalWindowUnsat', mod), ignore_errors=True)
        for e in ('.olean', '.ilean'):
            p = os.path.join(lib, 'LocalWindowUnsat', mod + e)
            if os.path.exists(p):
                os.remove(p)


def swap(a):
    src, lib = os.path.join(a.stage, 'src'), os.path.join(a.stage, 'lib')
    built = {}
    if os.path.exists(os.path.join(a.stage, 'build.jsonl')):
        for line in open(os.path.join(a.stage, 'build.jsonl')):
            r = json.loads(line)
            built[r['module']] = r
    total_old = total_new = 0
    if a.commit and not os.path.exists(os.path.join(LIB, 'ProofPack.olean')):
        raise SystemExit('ProofPack.olean is not in the production lib: build it first '
                         '(guarded_lake_build.py --direct ProofPack), before any swap')
    for mod in a.modules:
        o = old_info(mod)
        new_o = os.path.join(lib, 'LocalWindowUnsat', mod + '.olean')
        new_i = new_o[:-6] + '.ilean'
        new_s = os.path.join(src, 'LocalWindowUnsat', mod + '.lean')
        r = built.get('LocalWindowUnsat.' + mod)
        ready = r is not None and r['ok'] and os.path.exists(new_o) and os.path.exists(new_i)
        if ready and not a.no_axioms_check:
            ready = sorted(r.get('axioms', [])) == ['Classical.choice', 'Quot.sound', 'propext']
        new_bytes = (os.path.getsize(new_o) + os.path.getsize(new_i)) if ready else 0
        keep = a.keep_src and os.path.exists(new_s)
        new_bytes += os.path.getsize(new_s) if keep and ready else 0
        total_old += o['bytes'] if ready else 0
        total_new += new_bytes
        rec = dict(module=mod, ready=ready, old_bytes=o['bytes'], old_files=len(o['files']), new_bytes=new_bytes,
                   freed=o['bytes'] - new_bytes if ready else 0, commit=a.commit)
        if a.commit and ready:
            dst = os.path.join(LIB, 'LocalWindowUnsat', mod)
            # 1. the main source first: the packed one, or none (the .olean is all that importers
            #    need; guarded_lake_build.py --trust-mtime then treats the module as prebuilt).
            #    The old one must go: its imports name the Check modules.  The source is written
            #    before the .olean so that --trust-mtime finds the .olean up to date.
            main = os.path.join(FINAL, 'LocalWindowUnsat', mod + '.lean')
            if keep:
                shutil.copyfile(new_s, main + '.new')
                os.replace(main + '.new', main)
            else:
                os.remove(main)
            # 2. the new .olean/.ilean next to the old ones, then renamed over them (atomic)
            for s, e in ((new_i, '.ilean'), (new_o, '.olean')):
                shutil.copyfile(s, dst + e + '.new')
                os.replace(dst + e + '.new', dst + e)
            # 3. the old Data/Check build files and Check sources
            shutil.rmtree(dst, ignore_errors=True)
            shutil.rmtree(os.path.join(FINAL, 'LocalWindowUnsat', mod), ignore_errors=True)
            # 4. the staged copies
            for p in (new_o, new_i, *([new_s] if os.path.exists(new_s) else [])):
                os.remove(p)
        elif a.verbose:
            rec['would_delete'] = [os.path.relpath(f, ROOT) for f in o['files']]
        log(a, 'swap', rec)
    print(json.dumps(dict(modules=len(a.modules), old_bytes=total_old, new_bytes=total_new,
                          freed=total_old - total_new, commit=a.commit)), flush=True)


def agg(a):
    """The same source against the old and the staged replays.  Lean resolves `LocalWindowUnsat.*`
    by the first LEAN_PATH entry with a `LocalWindowUnsat/` directory, so with S/lib first every
    replay the file imports must be staged."""
    res = {}
    for tag, first in (('old', []), ('packed', [os.path.join(a.stage, 'lib')])):
        out = os.path.join(a.stage, 'agg_' + tag)
        os.makedirs(out, exist_ok=True)
        for f in a.modules:
            f = os.path.abspath(f)
            mod = os.path.basename(f)[:-5]
            lp = ':'.join(first + [LIB, out])
            wait_resources(a)
            st, txt, ru, wall, killed = measure.run_lean(
                ['--root=' + os.path.dirname(f), '-o', os.path.join(out, mod + '.olean'), f], dict(os.environ, LEAN_PATH=lp))
            o = os.path.join(out, mod + '.olean')
            rec = dict(tag=tag, module=mod, src_sha256=hashlib.sha256(open(f, 'rb').read()).hexdigest(),
                       LEAN_PATH=lp.replace(a.stage, '$S'), ok=st == 0 and not killed,
                       cpu=round(ru.ru_utime + ru.ru_stime, 2), rss_gb=round(ru.ru_maxrss / 1e6, 3),
                       olean_sha256=hashlib.sha256(open(o, 'rb').read()).hexdigest() if st == 0 else None,
                       output=txt.replace(a.stage, '$S'))
            res[(tag, mod)] = rec
            log(a, 'agg', rec)
    for f in a.modules:
        mod = os.path.basename(f)[:-5]
        print(json.dumps(dict(module=mod, both_ok=res[('old', mod)]['ok'] and res[('packed', mod)]['ok'],
                              identical_olean=res[('old', mod)]['olean_sha256'] == res[('packed', mod)]['olean_sha256'])))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('cmd', choices=['gen', 'build', 'old', 'swap', 'agg'])
    ap.add_argument('--stage', required=True, help='staging root (src/, lib/, oldlib/, *.jsonl)')
    ap.add_argument('--work', help='gen: LRAT/CNF working directory')
    ap.add_argument('--seeds', type=int, default=2)
    ap.add_argument('--rounds', type=int, default=0, help='gen: 0 = the set default (Q 1, R 2)')
    ap.add_argument('--allow-different', action='store_true',
                    help='gen: accept a proof whose counts differ from the old replay')
    ap.add_argument('--axioms', action='store_true', help='build: #print axioms of each unsat')
    ap.add_argument('--drop-src', action='store_true', help='build: delete each staged source once compiled')
    ap.add_argument('--commit', action='store_true', help='swap: really change the production files')
    ap.add_argument('--keep-src', action='store_true', help='swap: install the packed source as the main source')
    ap.add_argument('--no-axioms-check', action='store_true')
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--min-disk-mb', type=float, default=350)
    ap.add_argument('--min-avail-gb', type=float, default=4)
    ap.add_argument('--rss-cap-gb', type=float, default=2.9, help='kill a lean process above this RSS')
    ap.add_argument('modules', nargs='+', help='window modules (Q… / R…), or @FILE with one per line; agg: .lean files')
    a = ap.parse_args()
    mods = []
    for m in a.modules:
        mods += [x.strip() for x in open(m[1:]) if x.strip()] if m.startswith('@') else [m]
    a.modules = mods
    a.stage = os.path.abspath(a.stage)
    os.makedirs(a.stage, exist_ok=True)
    measure.CAP_KB = a.rss_cap_gb * 1e6
    {'gen': gen, 'build': build, 'old': old, 'swap': swap, 'agg': agg}[a.cmd](a)


if __name__ == '__main__':
    main()
