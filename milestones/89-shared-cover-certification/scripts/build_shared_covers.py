"""Generate all shared cover trees and independently replay every count code."""
from pathlib import Path
import gzip, hashlib, json, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT / 'milestones/88-retention-diagram-certificate'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
start = time.monotonic()
bp = OLD / 'data/box-cover-selected-max-gain.json.gz'
gp = ROOT / 'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
assert sha(bp) == 'c81ab4d006d9f40e74b1b3ed1c655b11282e96db8bd8242975042414f7090e93'
assert sha(gp) == '5ded4dbe27d3ba795e57e241289facce6444789e30edb9531a312fab58818823'
b = json.loads(gzip.decompress(bp.read_bytes()))
g = json.loads(gzip.decompress(gp.read_bytes()))
diagram = g['nodes']
for part in ['lean', 'data', 'logs', 'build']:
    (HERE / part).mkdir(exist_ok=True, parents=True)
symbols = [tuple(code // 6**j % 6 + 1 for j in range(5, -1, -1)) for code in range(46656)]


def step(node, x):
    return node if node < 2 else diagram[node - 2][x]


def write_fixed(path, raw):
    if path.exists():
        assert path.read_bytes() == raw, ('Changed generated file', str(path))
    else:
        path.write_bytes(raw)


classes = []
for case in b['class_intersections']:
    number = case['dag_set']
    label = f'{number:03d}'
    boxes = [b['box_catalogue'][r['box']] for r in case['selected']]
    root = g['roots'][number]
    trees, ids = [], {}
    calls = [0]

    def intern(key):
        if key not in ids:
            ids[key] = len(trees)
            trees.append(key)
        return ids[key]

    def build(pref, node, candidates):
        calls[0] += 1
        depth = len(pref)
        if node == 1:
            return intern(('accept',))
        for i in candidates:
            if all(lo == 1 and hi == 6 for lo, hi in boxes[i][depth:]):
                assert all(lo <= x <= hi for x, (lo, hi) in zip(pref, boxes[i]))
                return intern(('reject', i))
        assert depth < 6, (number, pref, node)
        children = tuple(build(pref + [x], step(node, x),
                               [i for i in candidates if boxes[i][depth][0] <= x <= boxes[i][depth][1]])
                         for x in range(1, 7))
        return intern(('split', *children))

    tree = build([], root, list(range(len(boxes))))
    accepted = 0
    for xs in symbols:
        ci, node, depth = tree, root, 0
        while trees[ci][0] == 'split':
            ci = trees[ci][xs[depth]]
            node = step(node, xs[depth])
            depth += 1
        # Independently evaluate the entire membership diagram too.
        fullnode = root
        for x in xs:
            fullnode = step(fullnode, x)
        if trees[ci][0] == 'accept':
            assert node == fullnode == 1
            accepted += 1
        else:
            box = boxes[trees[ci][1]]
            assert fullnode == 0 and all(lo <= x <= hi for x, (lo, hi) in zip(xs, box))
    header = ('import GraphData\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
              'namespace Snake9.Shared89\nopen Snake9.Boxes88 Snake9.Certificate88\n\n')
    data = header + f'def boxes{label} : List Box := [\n'
    data += ',\n'.join('[' + ','.join(f'({lo},{hi})' for lo, hi in box) + ']' for box in boxes)
    data += f'\n]\n\ndef root{label} : Nat := {root}\n\n'
    for i, item in enumerate(trees):
        if item[0] == 'accept':
            value = 'CoverTree.accept'
        elif item[0] == 'reject':
            value = f'CoverTree.reject {item[1]}'
        else:
            value = 'CoverTree.split [' + ','.join(f'tree{label}_{j}' for j in item[1:]) + ']'
        data += f'def tree{label}_{i} : CoverTree := {value}\n'
    data += f'def tree{label} : CoverTree := tree{label}_{tree}\n\nend Snake9.Shared89\n'
    data_path = HERE / 'lean' / f'Cover{label}Data.lean'
    write_fixed(data_path, data.encode())
    checks = (f'import Cover{label}Data\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
              'namespace Snake9.Shared89\nopen Snake9.Boxes88 Snake9.Certificate88\n\n'
              f'theorem cover{label} : checkCover retainedDiagram boxes{label} 6 [] root{label} tree{label} = true := by\n'
              '  decide +kernel\n\n'
              f'#print axioms cover{label}\nend Snake9.Shared89\n')
    check_path = HERE / 'lean' / f'Cover{label}Checks.lean'
    write_fixed(check_path, checks.encode())
    certificate = dict(dag_set=number, root=root, box_ids=[r['box'] for r in case['selected']],
                       trees=trees, tree=tree, context_count=len(case['contexts']))
    cp = HERE / 'data' / f'cover{label}-certificate.json.gz'
    write_fixed(cp, gzip.compress(json.dumps(certificate, separators=(',', ':')).encode(), mtime=0))
    classes.append(dict(dag_set=number, root=root, boxes=len(boxes), unique_tree_nodes=len(trees),
                        expanded_node_visits=calls[0], pointwise_checks=46656, accepted_codes=accepted,
                        context_count=len(case['contexts']), certificate_sha256=sha(cp),
                        source_sha256={data_path.name: sha(data_path), check_path.name: sha(check_path)}))
    if number % 10 == 0:
        print('GENERATED', number, 'boxes', len(boxes), 'nodes', len(trees), flush=True)

assert len(classes) == 127
assert sum(r['boxes'] for r in classes) == 82659
assert sum(r['context_count'] for r in classes) == 791
report = dict(status='GENERATED_ALL_SHARED_COVERS_KERNEL_CHECKS_PENDING', classes=classes,
              pointwise_checks=127 * 46656,
              input_sha256={str(p.relative_to(ROOT)): sha(p) for p in [bp, gp]},
              script_sha256=sha(Path(__file__)), seconds=time.monotonic() - start,
              scope='All shared cover sources generated and pointwise checked computationally. '
                    'Each Lean check still needs successful compilation; context witnesses and saved-row identity are separate.')
(HERE / 'data/shared-cover-generation.json').write_text(json.dumps(report, indent=2) + '\n')
print(report['status'], len(classes), 'classes', round(report['seconds'], 3), 'seconds', flush=True)
