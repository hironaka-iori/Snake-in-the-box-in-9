"""Generate balanced table literals without changing the existing cover trees."""
from pathlib import Path
import gzip, hashlib, json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
bp = ROOT / 'milestones/88-retention-diagram-certificate/data/box-cover-selected-max-gain.json.gz'
gp = ROOT / 'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
generation_path = HERE / 'data/shared-cover-generation.json'
generation = json.loads(generation_path.read_text())
for p in [bp, gp]:
    assert sha(p) == generation['input_sha256'][str(p.relative_to(ROOT))]
b = json.loads(gzip.decompress(bp.read_bytes()))
g = json.loads(gzip.decompress(gp.read_bytes()))


def balanced(values, render):
    if not values:
        return 'Table.empty'
    if len(values) == 1:
        return '(Table.leaf ' + render(values[0]) + ')'
    half = len(values) // 2
    return f'(Table.node {half} ' + balanced(values[:half], render) + ' ' + balanced(values[half:], render) + ')'


sources = {}


def write(name, text):
    p = HERE / 'lean' / (name + '.lean')
    raw = text.encode()
    if p.exists():
        assert p.read_bytes() == raw, ('changed generated file', name)
    else:
        p.write_bytes(raw)
    sources[p.name] = sha(p)


settings = '\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
namespace = 'namespace Snake9.Shared89\nopen Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89\n\n'
end = '\nend Snake9.Shared89\n'
graph = 'import GraphData\nimport BalancedLookup\n' + settings + namespace
graph += 'def graphTable : Table (Array Nat) :=\n'
graph += balanced(g['nodes'], lambda row: '#[' + ','.join(map(str, row)) + ']') + '\n'
write('BalancedGraphData', graph + end)
checks = 'import BalancedGraphData\n' + settings + namespace
checks += '''theorem graphTable_valid : check graphTable = true := by decide +kernel

theorem graphTable_flat : flatten graphTable = retainedDiagram.toList := by decide +kernel

def advanceBalanced (node symbol : Nat) : Nat :=
  if node < 2 then node else (lookup graphTable (node-2) #[]).getD symbol 0

theorem advanceBalanced_eq (node symbol : Nat) :
    advanceBalanced node symbol = nextNode retainedDiagram node symbol := by
  simp only [advanceBalanced, nextNode,
    lookup_eq_list graphTable retainedDiagram.toList graphTable_valid graphTable_flat]
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

#print axioms graphTable_valid
#print axioms graphTable_flat
#print axioms advanceBalanced_eq
'''
write('BalancedGraphChecks', checks + end)
for cls in b['class_intersections']:
    n = cls['dag_set']
    label = f'{n:03d}'
    boxes = [b['box_catalogue'][row['box']] for row in cls['selected']]
    data = f'import Cover{label}Data\nimport BalancedLookup\n' + settings + namespace
    data += f'def boxTable{label} : Table Box :=\n'
    data += balanced(boxes, lambda box: '[' + ','.join(f'({lo},{hi})' for lo, hi in box) + ']') + '\n'
    write(f'Balanced{label}Data', data + end)
    code = f'import Balanced{label}Data\nimport BalancedGraphChecks\nimport LookupCover\n' + settings + namespace
    code += f'''theorem boxTable{label}_valid : check boxTable{label} = true := by decide +kernel

theorem boxTable{label}_flat : flatten boxTable{label} = boxes{label} := by decide +kernel

theorem balancedCover{label} :
    checkCoverLookup advanceBalanced {len(boxes)} (fun i => lookup boxTable{label} i [])
      6 [] root{label} tree{label} = true := by decide +kernel

theorem originalCover{label} :
    checkCover retainedDiagram boxes{label} 6 [] root{label} tree{label} = true := by
  apply lookup_cover_to_original advanceBalanced {len(boxes)} (fun i => lookup boxTable{label} i [])
    retainedDiagram boxes{label} root{label} tree{label}
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable{label} boxes{label} boxTable{label}_valid boxTable{label}_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover{label}

#print axioms boxTable{label}_valid
#print axioms boxTable{label}_flat
#print axioms balancedCover{label}
#print axioms originalCover{label}
'''
    write(f'Balanced{label}Checks', code + end)
report = dict(status='GENERATED_BALANCED_TABLE_SOURCES_KERNEL_CHECKS_PENDING',
              source_sha256=sources, classes=127, graph_rows=len(g['nodes']),
              input_sha256={str(p.relative_to(ROOT)): sha(p) for p in [bp, gp, generation_path]},
              script_sha256=sha(Path(__file__)),
              scope='Alternative table representation for the unchanged shared cover equations. '
                    'Validity, flattening identities and cover equations require Lean checks.')
(HERE / 'data/balanced-cover-generation.json').write_text(json.dumps(report, indent=2) + '\n')
print(report['status'], len(sources), 'sources')
