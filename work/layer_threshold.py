import json
from pathlib import Path
from layer_search import solve_complement
vertices=json.loads(Path('outputs/snake8_witness.json').read_text())['vertex_sequence']
reports=[]
for target in [93,92,91]:
    reports.extend(solve_complement(vertices,30,target))
    Path('outputs/layer_threshold.json').write_text(json.dumps(reports,indent=2))
    if any('witness' in r for r in reports): break
