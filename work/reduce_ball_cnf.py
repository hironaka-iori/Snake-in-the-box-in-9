"""Replace prefix counters in the first core by direct endpoint triples.

This is a certificate-generation heuristic, not a trusted proof transformation.
The resulting CNF gets its own SAT certificate and independent Lean proof.
"""
import json
from itertools import combinations
from pathlib import Path

core = json.loads(Path('outputs/ball_certificate_core.json').read_text(encoding='utf-8'))
base = json.loads(Path('outputs/ball_certificate.json').read_text(encoding='utf-8'))
all_ends = {v for k, v in base['variables'].items() if k.startswith('end')}
ends = sorted({abs(v) for cl, reason in zip(core['clauses'], core['reasons'])
               if reason[0].startswith('counter_') for v in cl if abs(v) in all_ends})
items = [(cl, reason) for cl, reason in zip(core['clauses'], core['reasons'])
         if not reason[0].startswith('counter_')]
items += [([-a, -b, -c], ['endpoint_triple', [a, b, c]])
          for a, b, c in combinations(ends, 3)]
clauses = [item[0] for item in items]
data = {'variables': base['variables'], 'clauses': clauses,
        'reasons': [item[1] for item in items], 'endpoint_variables': ends,
        'scope': 'Reduced clause model; encoding soundness remains unproved.'}
Path('outputs/ball_direct.json').write_text(json.dumps(data, indent=2), encoding='utf-8')
n = max(abs(v) for cl in clauses for v in cl)
Path('outputs/ball_direct.cnf').write_text(
    f'p cnf {n} {len(clauses)}\n' + ''.join(
        ' '.join(map(str, cl)) + ' 0\n' for cl in clauses), encoding='utf-8')
print(f'{len(ends)} endpoint indicators, {len(clauses)} clauses')
