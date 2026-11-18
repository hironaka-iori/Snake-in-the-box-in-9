"""Write the 623 closed cut inequalities as reproducible Lean declarations."""
import json
from pathlib import Path

here = Path(__file__).resolve().parent
bases = json.loads((here.parents[2]/'milestones/236-parity-exchange-frontier/data/bases.json').read_bytes())['bases']
rows = json.loads((here/'decisions.json').read_bytes())
cuts = json.loads((here/'cuts.json').read_bytes())
assert len(cuts) == len(rows) == 623
folder = here/'certificates'
folder.mkdir(exist_ok=True)
for start in range(0, len(cuts), 25):
    lines = ['import CubeCut', 'open CubeCut237', 'set_option autoImplicit false',
             'set_option maxRecDepth 10000', 'set_option maxHeartbeats 10000000', '']
    for k in range(start, min(start+25, len(rows))):
        i, d, a, b = rows[k]['descriptions'][0]
        u = (set(bases[i]['vertices'])-{d}) | {a,b}
        mask = sum(1 << v for v in u)
        cut = cuts[k]
        assert 512 not in cut['s'] and 512 in cut['t']
        s = cut['s']
        t = [v for v in cut['t'] if v != 512]
        lines.extend([f'-- Base {i}, deletion {d}, additions {a} and {b}.',
                      f'theorem cut237_{k:03} : violated {mask}',
                      f'    {s} {t} = true := by decide +kernel', ''])
    (folder/f'Cuts{start:03}.lean').write_text('\n'.join(lines),encoding='utf-8')
