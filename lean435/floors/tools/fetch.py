#!/usr/bin/env python3
"""Fetch the 4.19 sources of the floor closure (FLOORS.md) into ORIG, verified by git blob sha.

    python3 -I lean435/floors/tools/fetch.py ORIG CACHE

- 1,042 main modules: from origin/main at commit 32d14f72 through the GitHub API by blob sha
  (single blobs, or members of the 4 archives, themselves fetched by blob sha), each checked
  against the git blob sha of milestones/33-233-lean/data/main_floor_modules.json
  (reuses `Sources` of milestones/33-233-lean/scripts/port_main_floors.py).
- 19 branch modules (`source: "branch"`): copied from this branch's work/final_lean or
  work/spectral/stronger, checked against the same manifest's git blob sha, except `Snake9` and
  `DirectionWindowBridge`, whose branch files are supersets of main's (FLOORS.md, "Definitions").
Writes ORIG/FETCH-MANIFEST.tsv: module, origin, git blob, sha256.
"""
import sys, json, hashlib
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / 'milestones/33-233-lean/scripts'))
import port_main_floors as P

orig, cache = Path(sys.argv[1]), Path(sys.argv[2])
cache.mkdir(parents=True, exist_ok=True)
man = json.loads(P.MANIFEST.read_text())
mods = man['modules']
src = P.Sources(man, cache)
# FLOORS.md: this branch's Snake9 and DirectionWindowBridge are strict supersets of main's lean-core
# copies (identical shared declarations); as in the 4.19 port run the branch files are used.
SUPERSET = {'Snake9', 'DirectionWindowBridge'}
BRANCH_ROOTS = [REPO / 'work/final_lean', REPO / 'work/spectral/stronger']


def dest(m):
    return orig / (m.replace('.', '/') + '.lean')


def ok(data, e):
    return e['git_blob'] in (P.git_blob_sha(data), P.git_blob_sha(data.replace(b'\r\n', b'\n')))


rows = []
for m in man['order']:
    e = mods[m]
    if e['source'] == 'branch':
        f = next((r / (m.replace('.', '/') + '.lean') for r in BRANCH_ROOTS
                  if (r / (m.replace('.', '/') + '.lean')).exists()), None)
        assert f is not None, m
        data = f.read_bytes()
        if not ok(data, e) and m not in SUPERSET:
            raise SystemExit(f'{m}: branch file {f} does not match git blob {e["git_blob"]}')
        d = dest(m); d.parent.mkdir(parents=True, exist_ok=True); d.write_bytes(data)
        rows.append((m, str(f.relative_to(REPO)) + ('' if ok(data, e) else ' (superset of main ' + e['git_blob'][:8] + ')'),
                     P.git_blob_sha(data)))


def put(m):
    d = dest(m)
    if not (d.exists() and ok(d.read_bytes(), mods[m])):
        data = src.get(m)          # raises unless the git blob sha matches
        d.parent.mkdir(parents=True, exist_ok=True)
        d.write_bytes(data)
    s = mods[m]['source']
    return (m, 'main:' + (s['path'] if 'path' in s else s['archive'] + '!' + s['member']), mods[m]['git_blob'])


todo = [m for m in man['order'] if mods[m]['source'] != 'branch']
arch = [m for m in todo if 'blob' not in mods[m]['source']]
blob = [m for m in todo if 'blob' in mods[m]['source']]
rows += [put(m) for m in arch]
with ThreadPoolExecutor(8) as ex:
    rows += list(ex.map(put, blob))
with open(orig / 'FETCH-MANIFEST.tsv', 'w') as f:
    f.write('module\torigin\tgit_blob\tsha256\n')
    for m, o, g in sorted(rows):
        f.write(f'{m}\t{o}\t{g}\t{hashlib.sha256(dest(m).read_bytes()).hexdigest()}\n')
print(f'main commit {man["main_commit"]}: branch {len(rows) - len(todo)}, archive members {len(arch)}, '
      f'blobs {len(blob)}, all git blob shas verified')
