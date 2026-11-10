"""Which modules would `guarded_lake_build.py --direct --trust-mtime TARGET` rebuild?  Runs the
real `closure` and `uptodate` of work/guarded_lake_build.py (read only) and propagates: a module
is rebuilt when it is not up to date or one of its imports is rebuilt.

  python3 stale.py TARGET ...
"""
import importlib.util, json, sys
from pathlib import Path
GLB = Path(__file__).resolve().parents[3] / 'work' / 'guarded_lake_build.py'
spec = importlib.util.spec_from_file_location('glb', GLB)
G = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G)
for t in sys.argv[1:]:
    G.PREBUILT.clear()
    deps = G.closure([t], trust_mtime=True)
    rebuilt, seen = set(), set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in deps[m]:
            visit(d)
        if any(d in rebuilt for d in deps[m]) or not G.uptodate(m, deps[m]):
            rebuilt.add(m)
    visit(t)
    print(json.dumps(dict(target=t, closure=len(deps), prebuilt=len(G.PREBUILT), rebuilt=sorted(rebuilt))))
