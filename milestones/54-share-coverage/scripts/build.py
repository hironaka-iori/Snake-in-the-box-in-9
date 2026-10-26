"""Reconstruct the contributor's full product and add certified forward share rules."""
from pathlib import Path
import collections, gzip, hashlib, itertools, json, subprocess, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np = model.np
REF = '74ca83db9c218446211d4f24c5e5a07329fdd847'
LUMP = {i: (i, i) for i in range(1, 6)} | {6: (6, 21)}

def get(path):
    return subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'show', REF+':'+path], cwd=ROOT)

def key(ds, al):
    ds, al = tuple(ds), tuple(map(tuple, al))
    return min((model.canon(ds), al), (model.canon(ds[::-1]), al[::-1]))

def extract():
    listing = subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'ls-tree', '-r', '--name-only', REF,
        'milestones/10-window-aggregate/data'], cwd=ROOT).decode().splitlines()
    files = [(p, 'cache') for p in listing if '/oracle_cache' in p and p.endswith('.jsonl')]
    files += [(f'milestones/11-local-ceiling/{p}', 'first') for p in [
        's0_share_loop/share_oracle.jsonl', 's0_k6_ceiling/oracle5_extra.jsonl',
        's0_k6_ceiling/oracle6.jsonl', 'k6_loop/oracle_share.jsonl', 'k6_loop/oracle_plain.jsonl']]
    files += [(p, 'second') for p in ['milestones/22-global-arguments/k6_w3/data/plain_k6w3.jsonl',
        'milestones/22-global-arguments/k6_w3_loop/data/plain_loop.jsonl.gz',
        'milestones/23-k6-lean/full_product/oracle_full.jsonl']]
    files += [('milestones/23-k6-lean/share_bonus/oracle_share_bonus.jsonl', 'bonus')]
    states = {}; provenance = []
    upstream = HERE/'data/upstream'; upstream.mkdir(parents=True, exist_ok=True)
    for index, (path, mode) in enumerate(files):
        data = get(path)
        archive = upstream/f'{index:02d}.gz'
        archive.write_bytes(data if path.endswith('.gz') else gzip.compress(data, mtime=0))
        provenance.append(dict(path=path, mode=mode, sha256=hashlib.sha256(data).hexdigest(), archive=archive.name))
        text = gzip.decompress(data).decode() if path.endswith('.gz') else data.decode()
        for line in text.splitlines():
            try:
                row = json.loads(line)
            except ValueError:
                assert mode == 'cache'
                continue
            if mode == 'cache':
                if row['radius'] != 4:
                    continue
                status = row['status']
            elif mode == 'first':
                if row['kind'] != 'plain' and row['result'] != 'SAT':
                    continue
                status = row['result']
            else:
                if mode != 'bonus' and row.get('kind') not in ('plain', 'plainrange'):
                    continue
                status = row['result']
            k = key(row['dirs'], row['alpha']); old = states.get(k)
            assert {old, status} != {'SAT', 'UNSAT'}, (path, k)
            if old in (None, 'TIMEOUT'):
                states[k] = status
    lumped = {}
    for (ds, bounds), status in states.items():
        if not 2 <= len(bounds) <= 6:
            continue
        choices = [[s for s in range(1, 7) if lo <= LUMP[s][0] and LUMP[s][1] <= hi] for lo, hi in bounds]
        if all(len(c) == 1 and LUMP[c[0]] == b for c, b in zip(choices, bounds)):
            k = key(ds, [LUMP[c[0]] for c in choices])
            lumped[k] = status
    for (ds, bounds), status in states.items():
        if status != 'UNSAT' or not 2 <= len(bounds) <= 6:
            continue
        choices = [[s for s in range(1, 7) if lo <= LUMP[s][0] and LUMP[s][1] <= hi] for lo, hi in bounds]
        for counts in itertools.product(*choices):
            k = key(ds, [LUMP[c] for c in counts])
            assert lumped.get(k) != 'SAT', k
            lumped[k] = 'UNSAT'
    keys = sorted(k for k, status in lumped.items() if status == 'UNSAT')
    (HERE/'data/provenance.json').write_text(json.dumps(dict(ref=REF, files=provenance), indent=2)+'\n')
    (HERE/'data/all-keys.json').write_text(json.dumps(dict(keys=keys, scope='Pinned numerical ordinary UNSAT records; not all Lean checked.'), indent=2)+'\n')
    print('Reconstructed', len(keys), 'ordinary UNSAT keys', flush=True)
    raw = get('milestones/23-k6-lean/full_product/keys_235.json')
    (HERE/'data/keys_235.json').write_bytes(raw)
    return json.loads(raw)['keys'], keys

def build(keys, name, extra_rules=None, reverse_rules=False):
    shapes = list(model.words(7)); extensions = list(model.words(8)); sid = {s: i for i, s in enumerate(shapes)}
    assert len(shapes) == 34 and len(extensions) == 132
    nc, nt = 6**5, 6**6
    counts = np.array(list(itertools.product(range(1, 7), repeat=6)), dtype=np.int16)
    tables = {}
    for ds, bounds in keys:
        cs = [lo for lo, hi in bounds]
        assert all(LUMP[c] == tuple(b) for c, b in zip(cs, bounds))
        for word, values in [(ds, cs), (ds[::-1], cs[::-1])]:
            table = tables.setdefault(model.canon(word), np.zeros(6**len(cs), dtype=bool))
            table[int(model.code(np.array([values]))[0])] = True
    rules = [dict(directions=[0,1,2,3,1,4], counts=[3,3,3,6,5], lower=48, milestone=51),
             dict(directions=[0,1,2,3,4,5], counts=[3,6,2,3,6], lower=96, milestone=52),
             dict(directions=[0,1,2,0,3,4], counts=[6,3,6,3,3], lower=96, milestone=53),
             dict(directions=[0,1,2,3,4,5], counts=[4,6,2,3,6], lower=96, milestone=53)]
    rules += extra_rules or []
    if reverse_rules:
        rules += [dict(rule, directions=list(model.canon(rule['directions'][::-1])),
                       counts=rule['counts'][::-1], orientation='reversed') for rule in list(rules)]
    arrays = collections.defaultdict(list)
    for di, ds in enumerate(extensions):
        keep = np.ones(nt, dtype=bool)
        for width in range(2, 7):
            table = tables.get(model.canon(ds[-width-1:]))
            if table is not None:
                keep &= ~table[model.code(counts[:, -width:])]
        ids = np.flatnonzero(keep)
        bonus = np.zeros(len(ids), dtype=np.int16)
        for rule in rules:
            if model.canon(ds[-6:]) == tuple(rule['directions']):
                bonus = np.maximum(bonus, np.where(np.all(counts[ids, -5:] == rule['counts'], axis=1), rule['lower'], 0))
        arrays['U'].append(sid[model.canon(ds[:7])]*nc+ids//6)
        arrays['V'].append(sid[model.canon(ds[1:])]*nc+ids%nc)
        arrays['count'].append(counts[ids, -1]); arrays['share_lower'].append(bonus)
        arrays['direction'].append(np.full(len(ids), di, dtype=np.int16)); arrays['count_code'].append(ids)
    arrays = {k: np.concatenate(v) for k, v in arrays.items()}
    folder = HERE/name; (folder/'data').mkdir(parents=True, exist_ok=True); (folder/'build').mkdir(exist_ok=True)
    np.savez_compressed(folder/'build/graph.npz', **arrays)
    metadata = dict(states=len(shapes)*nc, edges=len(arrays['U']), keys=len(keys), direction_shapes=shapes,
        extensions=extensions, share_rules=rules, strengthened_edges=int((arrays['share_lower']>0).sum()),
        arrays_sha256={k: hashlib.sha256(v.tobytes()).hexdigest() for k, v in arrays.items()},
        scope='Finite six-count product. Forward share rules checked in Lean; full graph-to-snake assembly pending. All-known exclusions include numerical results.')
    (folder/'data/model.json').write_text(json.dumps(metadata, indent=2)+'\n')
    print(name, 'edges', metadata['edges'], 'share edges', metadata['strengthened_edges'], flush=True)

if __name__ == '__main__':
    (HERE/'data').mkdir(parents=True, exist_ok=True)
    base, all_keys = extract()
    build(base, 'base235')
    build(all_keys, 'all-known')
