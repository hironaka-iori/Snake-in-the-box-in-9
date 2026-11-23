"""Audit output witnesses and the necessary endpoint test without using native solver code."""
from collections import Counter
from pathlib import Path
import gzip
import json

here = Path(__file__).resolve().parent
data = gzip.decompress((here / 'sections.gz').read_bytes()).decode().splitlines()
def unpack(line):
    dim, count, size, *path = map(int, line.split())
    assert len(path) == len(set(path)) == size and all(0 <= x < 512 for x in path)
    parts = [[]]
    for x in path:
        if parts[-1] and (x ^ parts[-1][-1]).bit_count() != 1:
            parts.append([])
        parts[-1].append(x)
    assert len(parts) == count
    return parts

isolated = Counter()
large = {}
for i, line in enumerate(data):
    parts = unpack(line)
    if len(parts) < 7:
        continue
    owner = {x: index for index, p in enumerate(parts) for x in p}
    endpoints = {x for p in parts for x in (p[0], p[-1])}
    active = set()
    for index, p in enumerate(parts):
        for j, x in enumerate(p):
            neighbors = {x ^ (1 << b) for b in range(9)} & owner.keys()
            assert neighbors == set(p[max(0,j-1):j]) | set(p[j+1:j+2])
    for x in range(512):
        if x in owner:
            continue
        neighbors = [x ^ (1 << b) for b in range(9) if x ^ (1 << b) in owner]
        if 1 <= len(neighbors) <= 2 and all(y in endpoints for y in neighbors):
            active.update(owner[y] for y in neighbors)
    blocked = [j for j in range(len(parts)) if j not in active]
    isolated[bool(blocked)] += 1
    if i == 98:
        large = {"vertices":len(owner), "components":len(parts), "blocked_component_sizes":[len(parts[j]) for j in blocked]}

def check_path(p):
    assert len(set(p)) == len(p) and all(0 <= x < 512 for x in p)
    for j,v in enumerate(p):
        for i in range(j):
            assert ((p[i]^v).bit_count() == 1) == (i+1 == j)

notes = {}
for f in ('control','all','selected'):
    lines = (here / (f + '.log')).read_text().splitlines()
    for line in lines[:-1]:
        label, raw = line.split(' vertices ')
        p = list(map(int,raw.split()))
        check_path(p)
        assert len(p)-1 == int(label.split()[1])
    assert lines[-1].startswith('DONE')
    notes[f] = lines[-1]
    if f == 'control':
        assert len(p) == 192
indices = list(map(int,(here/'selected.rows').read_text().split()))
assert (here/'selected.sections').read_text().splitlines() == [data[i] for i in indices]
print(json.dumps({"native_runs":notes,"all_source_sections":len(data),"eligible":sum(isolated.values()),
                  "blocked_whole_section":isolated[True], "no_detected_blocked_component":isolated[False],
                  "row_98":large},indent=2))
