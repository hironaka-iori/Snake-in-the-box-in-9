"""Generate the first shared-class witness checks from the complete aligned data."""
from pathlib import Path
import gzip, hashlib, json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
path = ROOT / 'milestones/89-shared-cover-certification/data/context-witnesses.json.gz'
assert sha(path) == '5dd985dc9e31441f481881895a827b7d88d68864b5104f07483adaaf86932d51'
data = json.loads(gzip.decompress(path.read_bytes()))
contexts = [row for row in data['contexts'] if row[1] == 1]
assert [row[0] // 75 for row in contexts] == [1,3,307,308,310,312]
assert all(row[0] % 75 == 0 for row in contexts)
list_ids = sorted({row[2] for row in contexts})
assert list_ids == [1,3]
for i in list_ids:
    assert len(data['witness_lists'][i]) == len(data['classes'][1][1]) == 640
    assert all(data['witnesses'][w][0] != 3 for w in data['witness_lists'][i])


def witness(row):
    family, index, offset, reverse = row
    assert family < 3
    return f'Witness.{["reference","short","interval"][family]} {index} {offset} ' + ('true' if reverse else 'false')


source = ('import BoxWitness\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
          'namespace Snake9.Witness90\nopen Snake9.Boxes88\n\n')
for i in list_ids:
    source += f'def witnessList{i:03d} : List Witness := [\n'
    source += ',\n'.join(witness(data['witnesses'][w]) for w in data['witness_lists'][i]) + '\n]\n\n'
source += 'def class001Jobs : List (Nat × List Witness) := [\n'
source += ',\n'.join(f'({row[0] // 75},witnessList{row[2]:03d})' for row in contexts) + '\n]\n\n'
source += 'end Snake9.Witness90\n'
p = HERE / 'lean/Class001WitnessData.lean'
raw = source.encode()
if p.exists():
    assert p.read_bytes() == raw
else:
    p.write_bytes(raw)
report = dict(status='GENERATED_CLASS001_WITNESS_DATA', directions=[row[0] // 75 for row in contexts],
              histories=[0], witness_list_ids=list_ids, boxes=640, validity_occurrences=3840,
              source_sha256={p.name:sha(p)}, input_sha256={str(path.relative_to(ROOT)):sha(path)},
              script_sha256=sha(Path(__file__)),
              scope='Six direction-specific witness jobs with the unchanged class1 geometry. '
                    'Concrete validity and numeric membership still need Lean checks.')
(HERE / 'data/class001-generation.json').write_text(json.dumps(report, indent=2) + '\n')
print(report['status'], report['directions'])
