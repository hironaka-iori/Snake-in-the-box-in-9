"""What `work/guarded_lake_build.py --trust-mtime` does with a window whose replay changes from the
split layout (main + Check<g> + Data<k>) to one packed module, in a scratch copy of the layout.

The real `closure` and `uptodate` of guarded_lake_build.py run on a mock project (empty files
with chosen mtimes) for a window W imported by an aggregate Agg.  Nothing outside the scratch
directory is read or written apart from importing guarded_lake_build.py.

  python3 trust_mtime_sim.py SCRATCH_DIR
"""
import importlib.util, json, os, shutil, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GLB = HERE.parents[2] / 'work' / 'guarded_lake_build.py'
spec = importlib.util.spec_from_file_location('glb', GLB)
G = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G)

OLD_MAIN = 'import LocalWindowUnsat.W.Check1\n'
OLD_CHECK = 'import LocalWindowUnsat.W.Data0\nimport LocalWindowUnsat.W.Data1\n'
PACKED = 'import LratFast2_O4k\nimport LocalWindowCnf.W\nimport ProofPack\nimport NatPack\n'
LIBS = ['LratFast2_O4k', 'LocalWindowCnf.W', 'ProofPack', 'NatPack']


def setup(root, t, scenario):
    """t: base time.  Libraries at t, old window files at t+10, aggregate at t+20, the swap at t+30."""
    shutil.rmtree(root, ignore_errors=True)
    G.ROOT = root
    G.PREBUILT.clear()

    def src(m, txt, mt):
        p = G.module_path(m)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(txt)
        os.utime(p, (mt, mt))

    def olean(m, mt):
        p = G.olean_path(m)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text('')
        os.utime(p, (mt, mt))
    for m in LIBS:
        src(m, '', t)
        olean(m, t + (35 if scenario == 'keep-src, ProofPack built after the swap' and m == 'ProofPack' else 0))
    src('Agg', 'import LocalWindowUnsat.W\n', t + 20)
    olean('Agg', t + 20)
    if scenario == 'before':
        src('LocalWindowUnsat.W', OLD_MAIN, t + 10)
        src('LocalWindowUnsat.W.Check1', OLD_CHECK, t + 10)
        for m in ('LocalWindowUnsat.W', 'LocalWindowUnsat.W.Check1', 'LocalWindowUnsat.W.Data0',
                  'LocalWindowUnsat.W.Data1'):
            olean(m, t + 10)
        return
    olean('LocalWindowUnsat.W', t + 30)          # the packed .olean
    if scenario.startswith('swap'):              # migrate_qr.py swap --commit (no --keep-src)
        return
    if scenario.startswith('keep-src'):          # migrate_qr.py swap --commit --keep-src
        src('LocalWindowUnsat.W', PACKED, t + 29)
        return
    if scenario == 'stale main source, old build files deleted':
        src('LocalWindowUnsat.W', OLD_MAIN, t + 10)
        src('LocalWindowUnsat.W.Check1', OLD_CHECK, t + 10)
        return
    if scenario == 'stale main source, old build files kept':
        src('LocalWindowUnsat.W', OLD_MAIN, t + 10)
        src('LocalWindowUnsat.W.Check1', OLD_CHECK, t + 10)
        for m in ('LocalWindowUnsat.W.Check1', 'LocalWindowUnsat.W.Data0', 'LocalWindowUnsat.W.Data1'):
            olean(m, t + 10)
        return
    if scenario == 'packed source installed after the .olean':
        src('LocalWindowUnsat.W', PACKED, t + 31)
        return
    raise ValueError(scenario)


def main():
    root = Path(sys.argv[1]).resolve() / 'trust_mtime_sim'
    t = 1.7e9
    for scenario in ('before', 'swap', 'keep-src', 'keep-src, ProofPack built after the swap',
                     'packed source installed after the .olean',
                     'stale main source, old build files deleted', 'stale main source, old build files kept'):
        setup(root, t, scenario)
        try:
            deps = G.closure(['Agg'], trust_mtime=True)
        except SystemExit as e:
            print(json.dumps({'scenario': scenario, 'closure': 'error: %s' % e}))
            continue
        # replay the build loop: a module is skipped when up to date, else compiled; a compile
        # fails when an import has no .olean (here: a Data module whose files were deleted)
        state = {}
        order, seen = [], set()

        def visit(m):
            if m in seen:
                return
            seen.add(m)
            for d in deps[m]:
                visit(d)
            order.append(m)
        visit('Agg')
        for m in order:
            if any(state.get(d) in ('fails', 'blocked') for d in deps[m]):
                state[m] = 'blocked'
            elif G.uptodate(m, deps[m]):
                state[m] = 'up to date'
            else:
                imps = [l.split()[1] for l in G.module_path(m).read_text().splitlines()
                        if l.startswith('import ')] if G.module_path(m).exists() else []
                missing = [d for d in imps if not G.olean_path(d).exists() and state.get(d) != 'compiled']
                state[m] = 'fails' if missing else 'compiled'
                if missing:
                    state[m + ' (missing imports)'] = missing
        print(json.dumps({'scenario': scenario, 'prebuilt': sorted(G.PREBUILT),
                          'deps': {m: deps[m] for m in order}, 'result': state}))
    shutil.rmtree(root, ignore_errors=True)


if __name__ == '__main__':
    main()
