"""Generate balanced direction/reference tables with exact source-list comparisons."""
from pathlib import Path
import ast, gzip, hashlib, json, re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {}


def text(rel):
    p = ROOT / rel
    pins[rel] = sha(p)
    return p.read_text(encoding='utf-8-sig')


model = json.loads(text('milestones/59-extended-share-window/extended/data/model.json'))
directions = model['extensions']
source = text('milestones/77-direction-state-coverage/lean/DirectionTables.lean')
literal = source.split('def extensions :')[1].split(':=', 1)[1].split('\ndef sourceIds', 1)[0]
assert ast.literal_eval(literal.strip()) == directions
assert len(directions) == len(set(map(tuple, directions))) == 505
refs = json.loads(text('milestones/85-reference-catalogue-union/data/reference-union.json'))['rows']
keys = [(r['directions'], r['symbols']) for r in refs]
union = text('milestones/85-reference-catalogue-union/lean/ReferenceUnion.lean')
expr = union.split('def referenceKeys')[1].split(':=', 1)[1].split('\n', 1)[0]
assert re.findall(r'keys([0-9]{2})', expr) == [f'{i:02d}' for i in range(22)]
reconstructed = []
for i in range(22):
    name = f'{i:02d}'
    t = text(f'milestones/85-reference-catalogue-union/lean/ReferenceChunk{name}.lean')
    expr = t.split(f'def keys{name}')[1].split(':=', 1)[1].split('\ntheorem', 1)[0].strip()
    reconstructed.extend(ast.literal_eval(expr))
assert reconstructed == keys and len(keys) == 1378


def balanced(values, render):
    if not values:
        return 'Table.empty'
    if len(values) == 1:
        return '(Table.leaf ' + render(values[0]) + ')'
    half = len(values) // 2
    return f'(Table.node {half} ' + balanced(values[:half], render) + ' ' + balanced(values[half:], render) + ')'


for part in ['lean','data','logs','build']:
    (HERE / part).mkdir(exist_ok=True, parents=True)
fmt = lambda xs: '[' + ','.join(map(str, xs)) + ']'
source = ('import BalancedLookup\nimport BoxWitness\n\nset_option maxHeartbeats 0\n'
          'set_option maxRecDepth 100000\n\nnamespace Snake9.Witness90\n'
          'open Snake9.Balanced89 Snake9.Boxes88\n\n')
source += 'def directionTable : Table (List Nat) :=\n' + balanced(directions, fmt) + '\n\n'
source += 'def referenceTable : Table (List Nat × List Nat) :=\n'
source += balanced(keys, lambda key: '(' + fmt(key[0]) + ',' + fmt(key[1]) + ')') + '\n\n'
source += 'end Snake9.Witness90\n'
p = HERE / 'lean/WitnessTablesData.lean'
raw = source.encode()
if p.exists():
    assert p.read_bytes() == raw, 'Generated table source changed'
else:
    p.write_bytes(raw)
payload = dict(directions=directions, reference_keys=keys, input_sha256=pins)
packed = gzip.compress(json.dumps(payload, separators=(',', ':')).encode(), mtime=0)
(HERE / 'data/witness-tables.json.gz').write_bytes(packed)
report = dict(status='GENERATED_EXACT_BALANCED_WITNESS_TABLES', direction_count=505, reference_count=1378,
              source_sha256={p.name:sha(p)}, payload_sha256=hashlib.sha256(packed).hexdigest(),
              input_sha256=pins, script_sha256=sha(Path(__file__)),
              scope='Exact literal-order reconstruction and balanced table source generation. '
                    'Lean table validity and flattening identities remain pending.')
(HERE / 'data/witness-table-generation.json').write_text(json.dumps(report, indent=2) + '\n')
print(report['status'], '505 directions, 1378 reference keys')
