"""Which chain modules would `work/spectral/chain_audit.py --reuse --target T` recompile?  Uses
its own `order`, `src`, `imports` and `dep_mtime` (read only); a recompiled module makes its
importers recompile.  Core modules named with --assume-rebuilt count as freshly rebuilt.

  python3 chain_stale.py TARGET [--assume-rebuilt CORE_MODULE ...]
"""
import argparse, importlib.util, json
from pathlib import Path
CA = Path(__file__).resolve().parents[3] / 'work' / 'spectral' / 'chain_audit.py'
spec = importlib.util.spec_from_file_location('ca', CA)
C = importlib.util.module_from_spec(spec)
spec.loader.exec_module(C)
ap = argparse.ArgumentParser()
ap.add_argument('targets', nargs='+')
ap.add_argument('--assume-rebuilt', nargs='*', default=[])
a = ap.parse_args()
build = C.SPECTRAL / '.verification' / 'chain'
for t in a.targets:
    mods, re_ = C.order(t), set()
    for m in mods:
        o = build / (m + '.olean')
        imps = C.imports(m)
        if (not o.exists() or any(d in re_ or d in a.assume_rebuilt for d in imps)
                or o.stat().st_mtime <= max([C.src(m).stat().st_mtime, *(C.dep_mtime(d, build) for d in imps)])):
            re_.add(m)
    print(json.dumps(dict(target=t, modules=len(mods), recompiled=[m for m in mods if m in re_])))
