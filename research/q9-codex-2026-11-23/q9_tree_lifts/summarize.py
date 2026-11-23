"""Recheck Q8 donors, run coverage, and emitted Q9 witnesses from local logs."""
from pathlib import Path
from collections import Counter
import hashlib
import json

root = Path(__file__).resolve().parent
data = root.parent / 'q8_catalogue_96_98.words'
words = data.read_text().split()
def check(path, dimension):
    assert len(set(path)) == len(path) and all(0 <= x < 2**dimension for x in path)
    for j, x in enumerate(path):
        for i in range(j):
            assert ((x ^ path[i]).bit_count() == 1) == (i + 1 == j)

for w in words:
    p = [0]
    for c in w:
        p.append(p[-1] ^ (1 << int(c)))
    check(p, 8)

def rows(files):
    out = {}
    for f in files:
        for line in f.read_text().splitlines():
            fields = line.split()
            if fields[0] == 'FORESTS':
                continue
            assert fields[0] == 'ROW', (f, line)
            idx, *rest = map(int, fields[1:])
            assert idx not in out
            out[idx] = rest
    assert set(out) == set(range(len(words)))
    return out

direct = rows([root/'pilot.log', *sorted(root.glob('full_*.log'))])
rank8 = rows(sorted(root.glob('up196_keep94_*.log')))
rank7 = rows([root/'dependent94.log'])
assert all(v[1] == 531441 and v[0] == len(words[i])+1 and v[4] == 0 for i,v in direct.items())
assert all(v[0] == 531441 and v[1] == len(words[i])+1-94 and v[-2:] == [0,0] for i,v in rank8.items())
assert all(v[-1] == 0 for v in rank7.values())
out = dict(donor_sha256=hashlib.sha256(data.read_bytes()).hexdigest(),donor_lengths=Counter(map(len, words)),
           tree_donor_pairs=sum(v[1] for v in direct.values()),
           max_private_connectors={d:max(v[2] for i,v in direct.items() if len(words[i])==d) for d in set(map(len,words))},
           rank8_sums=list(map(sum,zip(*(v[2:] for v in rank8.values())))),
           rank7_sums=list(map(sum,zip(*rank7.values()))))
search = {}
blocks = {'651373':9,'129911':14,'472285':22}
for f in sorted([*root.glob('blocks_*.log'), *root.glob('flex_*.log')]):
    mode, seed = f.stem.split('_')
    best = 0
    for line in f.read_text().splitlines():
        s = line.split()
        if not s or s[0]!='BEST':
            continue
        idx, length = map(int,s[2:4])
        prefix = s[5] if mode=='blocks' else s[4]
        path = list(map(int,s[(6 if mode=='blocks' else 5):]))
        assert len(path) == length+1 and len(prefix)*2 == length
        assert words[idx].startswith(prefix) or words[idx][::-1].startswith(prefix)
        check(path, 9)
        groups={}
        for i,c in enumerate(prefix):
            m = path[2*i]^path[2*i+2]
            assert m.bit_count()==2
            if mode=='flex':
                assert m & (1<<int(c))
                continue
            block=(i+int(s[4]))//blocks[seed]
            g=groups.setdefault(block,{})
            assert g.setdefault(c,m)==m
        for g in groups.values():
            span={0}
            for m in g.values():
                assert m not in span
                span |= {x^m for x in span}
        best=max(best,length)
    search[f.stem]=best
out['verified_search_witness_lengths_at_snapshot']=search
print(json.dumps(out,indent=2))
