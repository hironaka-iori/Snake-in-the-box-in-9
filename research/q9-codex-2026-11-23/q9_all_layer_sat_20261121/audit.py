"""Pure-Python checker of seed paths, witnesses, selected pins and SAT outcomes."""
from pathlib import Path
import itertools
import json
import collections
import hashlib

base = Path(__file__).resolve().parent
def read(name):
    return list(map(json.loads,(base/name).read_text().splitlines()))

def check(word, sequence):
    vertices = set(sequence)
    assert all(0<=x<512 for x in sequence) and len(sequence)==len(vertices)
    layer_path = [h for h,g in itertools.groupby(x//32 for x in sequence)]
    actual = [a^b for a,b in zip(layer_path,layer_path[1:])]
    assert layer_path[0]==0 and len(set(layer_path))==16
    assert actual==[2**int(t) for t in word]
    index = {v:i for i,v in enumerate(sequence)}
    for i,v in enumerate(sequence):
        adjacent = {index[v^(2**d)] for d in range(9) if (v^(2**d)) in index}
        assert adjacent == {j for j in [i-1,i+1] if 0<=j<len(sequence)}
    used = [{v%32 for v in vertices if v//32==l} for l in layer_path]
    for i,j in itertools.combinations(range(16),2):
        if (layer_path[i]^layer_path[j]).bit_count()==1:
            assert len(used[i]&used[j])==int(i+1==j)

seeds=json.loads((base/'seed_paths.json').read_text())
for w,p in seeds.items():check(w,p)
ctrl = read('controls0.jsonl')+read('controls6.jsonl')
positive=[]
for r in ctrl:
    if r['status']=='SAT':
        p=r['path'];check(r['word'],p);assert len(p)>=r['target_vertices']
        positive.append([r['word'],len(p)-1,r['positive_pins'],len(set(p)^set(seeds[r['word']]))])
pinned={r['word']:r for r in read('results4.jsonl')+read('results4_retry.jsonl')}
assert set(pinned)==set(seeds) and all(r['status']=='UNSAT' and r['positive_pins']==64 for r in pinned.values())
deep=read('all_free10k.jsonl')
assert len(deep)==98 and {r['word'] for r in deep}==set(seeds)
c=json.loads((base/'certificate.json').read_text())
assert len(set(c['cube_vertices']))==c['positive_pins'] and set(c['cube_vertices'])<=set(seeds[c['word']])
assert 's VERIFIED' in (base/'drat.log').read_text()
print(json.dumps(dict(seeds=len(seeds),controls_word_edges_pins_symmetric_difference=positive,
    fixed64=len(pinned), free10000=dict(collections.Counter(r['status'] for r in deep)),
    fixed32_word=c['word'],certificate_status='VERIFIED',
    certificate_sha256=hashlib.sha256((base/'core.drat').read_bytes()).hexdigest()),indent=2))
