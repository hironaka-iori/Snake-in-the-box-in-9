"""Generate the same six-job pilot with explicit reusable reference-shape indices."""
from pathlib import Path
import gzip, hashlib, json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PREV = HERE.parent / '90-context-witness-certificates'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {}


def load(rel, compressed=False):
    p = ROOT / rel
    pins[rel] = sha(p)
    raw = p.read_bytes()
    return json.loads(gzip.decompress(raw) if compressed else raw)


data = load('milestones/89-shared-cover-certification/data/context-witnesses.json.gz', True)
assert pins['milestones/89-shared-cover-certification/data/context-witnesses.json.gz'] == '5dd985dc9e31441f481881895a827b7d88d68864b5104f07483adaaf86932d51'
tables = load('milestones/90-context-witness-certificates/data/witness-tables.json.gz', True)
old = load('milestones/90-context-witness-certificates/data/class001-generation.json')
for rel, digest in old['input_sha256'].items():
    assert sha(ROOT / rel) == digest
for name, digest in old['source_sha256'].items():
    p = PREV / 'lean' / name
    assert sha(p) == digest
    pins[p.relative_to(ROOT).as_posix()] = digest
for name in ['Class001WitnessChecks', 'WitnessTablesChecks', 'WitnessFactors']:
    p = PREV / 'data' / (name + '-audit.json')
    r = load(p.relative_to(ROOT).as_posix())
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    assert sha(PREV / 'lean' / (name + '.lean')) == r['source_sha256']
refs = tables['reference_keys']
directions = tables['directions']


def canon(word):
    labels = {}
    return [labels.setdefault(x, len(labels)) for x in word]


pool, pool_ids, jobs = [], {}, []
for block, cls, list_id in data['contexts']:
    if cls != 1:
        continue
    assert block % 75 == 0
    di = block // 75
    indices, reference_entries = [], 0
    for wi in data['witness_lists'][list_id]:
        family, ki, offset, reverse = data['witnesses'][wi]
        assert family < 3
        if family != 0:
            indices.append(0)
            continue
        reference_entries += 1
        pattern, symbols = refs[ki]
        shape = (di, offset+2, len(symbols)+1, bool(reverse), tuple(pattern))
        piece = directions[di][shape[1]:shape[1]+shape[2]]
        assert canon(piece[::-1] if reverse else piece) == pattern
        if shape not in pool_ids:
            pool_ids[shape] = len(pool)
            pool.append(shape)
        indices.append(pool_ids[shape])
    assert len(indices) == 640 and reference_entries == 622
    jobs.append(dict(direction=di, list_id=list_id, indices=indices, reference_entries=reference_entries))
assert [r['direction'] for r in jobs] == [1,3,307,308,310,312]
assert len(pool) == 156
for job in jobs:
    for wi, ci in zip(data['witness_lists'][job['list_id']], job['indices']):
        family, ki, offset, reverse = data['witnesses'][wi]
        if family == 0:
            pattern, symbols = refs[ki]
            assert pool[ci] == (job['direction'],offset+2,len(symbols)+1,bool(reverse),tuple(pattern))


def balanced(values):
    if not values:
        return 'Table.empty'
    if len(values) == 1:
        di, offset, width, reverse, pattern = values[0]
        shape = f'(Shape.mk {di} {offset} {width} ' + str(reverse).lower() + ' ' + fmt(pattern) + ')'
        return '(Table.leaf ' + shape + ')'
    half = len(values) // 2
    return f'(Table.node {half} ' + balanced(values[:half]) + ' ' + balanced(values[half:]) + ')'


fmt = lambda xs: '[' + ','.join(map(str, xs)) + ']'
for folder in ['lean','data','build','logs','audit']:
    (HERE / folder).mkdir(parents=True, exist_ok=True)
source = ('import ShapeCache\nimport BalancedLookup\nimport Class001WitnessData\n\n'
          'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
          'namespace Snake9.Shape91\nopen Snake9.Balanced89 Snake9.Witness90 Snake9.Boxes88\n\n')
source += 'def pilotShapeCount : Nat := 156\n\n'
source += 'def pilotShapeTable : Table Shape :=\n' + balanced(pool) + '\n\n'
source += 'def pilotShapeAt (i : Nat) : Shape := lookup pilotShapeTable i (Shape.mk 0 0 0 false [])\n\n'
for job in jobs:
    source += f"def indices{job['direction']:03d} : List Nat := {fmt(job['indices'])}\n\n"
source += 'def pilotIndices (di : Nat) : List Nat :=\n  match di with\n'
source += ''.join(f"  | {job['direction']} => indices{job['direction']:03d}\n" for job in jobs)
source += '  | _ => []\n\n'
source += 'def pilotCountLists : List (List Witness) := [witnessList001,witnessList003]\n\n'
source += 'end Snake9.Shape91\n'
path = HERE / 'lean/CachePilotData.lean'
assert not path.exists() or path.read_bytes() == source.encode(), 'Existing generated source differs'
path.write_bytes(source.encode())
baseline = PREV / 'lean/Class001WitnessChecks.lean'
baseline_copy = HERE / 'lean/DirectPilotChecks.lean'
assert not baseline_copy.exists() or baseline_copy.read_bytes() == baseline.read_bytes()
baseline_copy.write_bytes(baseline.read_bytes())
pins[baseline.relative_to(ROOT).as_posix()] = sha(baseline)
payload = dict(shapes=pool, jobs=jobs, input_sha256=pins)
packed = gzip.compress(json.dumps(payload, separators=(',', ':')).encode(), mtime=0)
(HERE / 'data/cache-pilot.json.gz').write_bytes(packed)
report = dict(status='GENERATED_REFERENCE_SHAPE_REUSE_PILOT', directions=[r['direction'] for r in jobs],
              jobs=6, count_lists=2, entries=3840, reference_entries=3732, shape_tests=156,
              nonreference_entries=108, payload_sha256=hashlib.sha256(packed).hexdigest(),
              source_sha256={p.name:sha(p) for p in [path,baseline_copy]},
              input_sha256=pins, script_sha256=sha(Path(__file__)),
              scope='Same six class1 jobs and original witness lists. Shape indices are proposals; '
                    'Lean must check every requested descriptor and every cached shape.')
(HERE / 'data/pilot-generation.json').write_text(json.dumps(report, indent=2)+'\n')
print(report['status'], '3732 reference entries, 156 reusable shape tests')
