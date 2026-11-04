"""Rebuild weights in batches, reusing the exact accepted retained-row mask.

This does not re-prove the geometric validity of the mask. The caller must
match both old144 and complete156 weight hashes before changing the floor.
"""
from pathlib import Path
import hashlib
import json

R = Path(__file__).resolve().parents[3]

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def canon(word):
    names = {}
    return ''.join(str(names.setdefault(int(x), len(names))) for x in word)

def shape(word):
    return min(canon(word), canon(word[::-1]))

def reconstruct(np):
    pins = {}
    def read(rel):
        pins[rel] = digest(R/rel)
        return json.loads((R/rel).read_text(encoding='utf-8-sig'))
    meta = read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
    rel = 'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
    pins[rel] = digest(R/rel)
    with np.load(R/rel, allow_pickle=False) as z:
        arrays = {k:z[k] for k in ['U','V','weight','direction','count_code']}
    for k,a in arrays.items():
        assert a.ndim == 1 and len(a) == 4947008
        assert hashlib.sha256(memoryview(np.ascontiguousarray(a)).cast('B')).hexdigest() == meta['arrays_sha256'][k], k
    ds = read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
    completed = read('milestones/73-countfree-share-catalogue/data/proved-model.json')
    rules = read('milestones/120-nine-transition-window/data/full-rules.json')
    removed = read('milestones/144-countfree-share18/data/share18-impact/removed-indices.json')
    mask = np.ones(4947008, dtype=bool)
    assert len(removed) == 4947008-4661572 and len(set(removed)) == len(removed)
    assert min(removed) >= 0 and max(removed) < len(mask)
    mask[np.asarray(removed, dtype=np.int64)] = False
    del removed
    digits = np.empty((4947008, 6), dtype=np.int16)
    shared = np.zeros(4947008, dtype=np.int64)
    direction = arrays['direction']
    assert np.all(direction[:-1] <= direction[1:])
    assert int(direction.min()) == 0 and int(direction.max()) == len(ds)-1
    for index, word in enumerate(ds):
        begin, end = np.searchsorted(direction, [index,index+1])
        suffix = word[3:9]
        assert list(suffix) == list(word[-6:])
        suffix_shape = shape(suffix)
        matching = [rule for rule in rules if shape(rule['directions']) == suffix_shape]
        for lo in range(int(begin), int(end), 65536):
            hi = min(lo+65536, int(end))
            codes = arrays['count_code'][lo:hi].astype(np.int64)
            counts = np.column_stack([codes//6**j%6+1 for j in range(5,-1,-1)]).astype(np.int16)
            digits[lo:hi] = counts
            five = counts[:,1:6]
            if canon(suffix) != suffix_shape:
                five = five[:,::-1]
            bonus = np.zeros(hi-lo, dtype=np.int64)
            for rule in matching:
                lower = np.asarray([b[0] for b in rule['bounds']], dtype=np.int16)
                upper = np.asarray([b[1] for b in rule['bounds']], dtype=np.int16)
                applicable = np.all((five >= lower) & (np.where(five == 6,21,five) <= upper), axis=1)
                credit = 24*np.maximum(0, rule['lower']-five[:,rule['positions']].sum(axis=1))
                bonus = np.maximum(bonus, np.where(applicable, credit, 0))
            if suffix_shape == '012032':
                bonus = np.maximum(bonus, 24*np.maximum(0,9-counts[:,2]-counts[:,4]))
            if shape(word[2:]) == shape([0,1,2,3,1,0,4]):
                credit = 24*np.maximum(0,25-counts.sum(axis=1))
                bonus = np.maximum(bonus, np.where(counts[:,0] < 6,credit,0))
            shared[lo:hi] = bonus
    return dict(arrays=arrays, meta=meta, ds=ds, mask=mask, shared=shared,
                digits=digits, completed=completed, pins=pins)
