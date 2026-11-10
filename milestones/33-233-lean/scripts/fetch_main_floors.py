"""Fetch main's floor modules into a project root for `work/guarded_lake_build.py --direct`.

    python3 -I fetch_main_floors.py ROOT ARCHIVE_CACHE

Every module of `data/main_floor_modules.json` that is not this branch's is fetched from
origin/main through the GitHub API by git blob sha (single blobs, or members of the four
archives committed on main, also fetched by blob sha) and checked against its recorded git
blob sha; it is written to ROOT/<path>.lean.  Branch modules with a built `.olean` (core or
chain) are left out, so they are leaves of the port's closure and are never rebuilt; the two
unbuilt branch modules (`LocalWindowTagsShare`, `...Packed`) are copied after a blob-sha check.
The script asserts that no fetched module shadows a source or `.olean` of this branch.
"""
import sys, json, hashlib
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / 'milestones/33-233-lean/scripts'))
import port_main_floors as P
root = Path(sys.argv[1]); cache = Path(sys.argv[2]); cache.mkdir(parents=True, exist_ok=True)
man = json.loads(P.MANIFEST.read_text()); mods = man['modules']
CORE = REPO / 'work/final_lean/.lake/build/lib/lean'; CHAIN = REPO / 'work/spectral/.verification/chain'
src = P.Sources(man, cache)
def dest(m): return root / (m.replace('.', '/') + '.lean')
todo, branch_copy = [], []
for m in man['order']:
    e = mods[m]
    if e['source'] == 'branch':
        if (CORE / (m.replace('.', '/') + '.olean')).exists() or (CHAIN / (m + '.olean')).exists():
            continue
        f = REPO / 'work/final_lean' / (m + '.lean')
        assert P.git_blob_sha(f.read_bytes()) == e['git_blob'], m
        branch_copy.append((m, f))
        continue
    # never shadow a branch module
    assert not (CORE / (m.replace('.', '/') + '.olean')).exists() and not (CHAIN / (m + '.olean')).exists(), m
    assert not (REPO / 'work/final_lean' / (m.replace('.', '/') + '.lean')).exists(), m
    assert not (REPO / 'work/spectral/stronger' / (m + '.lean')).exists(), m
    todo.append(m)
for m, f in branch_copy:
    d = dest(m); d.parent.mkdir(parents=True, exist_ok=True); d.write_bytes(f.read_bytes())
# archives first (serially), then blobs in parallel
arch = [m for m in todo if 'blob' not in mods[m]['source']]
blob = [m for m in todo if 'blob' in mods[m]['source']]
def put(m):
    d = dest(m)
    if d.exists() and mods[m]['git_blob'] in (P.git_blob_sha(d.read_bytes()), P.git_blob_sha(d.read_bytes().replace(b'\r\n', b'\n'))):
        return
    data = src.get(m)
    d.parent.mkdir(parents=True, exist_ok=True); d.write_bytes(data)
for m in arch: put(m)
with ThreadPoolExecutor(8) as ex: list(ex.map(put, blob))
print(f'branch copies {len(branch_copy)}, fetched archive members {len(arch)}, blobs {len(blob)}')
