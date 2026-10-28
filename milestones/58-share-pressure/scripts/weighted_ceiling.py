"""Test the best fixed five-centre weighting on the saved attaining cycle.

This is a limitation of a proposed relaxation, not a new snake bound.
"""
from pathlib import Path
from fractions import Fraction
import json

HERE = Path(__file__).resolve().parents[1]
geometry = json.loads((HERE / 'data/forced-geometry.json').read_text())['patterns']
lookup = {tuple(r['directions']): r for r in geometry}
analysis = json.loads((HERE / 'geometry/data/analysis-share.json').read_text())
cycle = analysis['cycle']
rows = []
for edge in cycle:
    g = lookup[tuple(edge['directions'])]
    individual = [sum(t['credit'] for t in g['terms'] if t['centre'] == x)
                  for x in g['centres']]
    assert sum(individual) == g['share_lower']
    base = edge['weight'] - edge['share_lower']
    # c + v_i weights: 5c + sum(v_i)=5, all coefficients nonnegative.
    # The six simplex vertices are uniform weights and each concentrated weight.
    features = [edge['weight']] + [base + 5 * a for a in individual]
    rows.append(dict(directions=edge['directions'], individual=individual,
                     vertex_weights=features))
means = [Fraction(sum(r['vertex_weights'][k] for r in rows), len(rows))
         for k in range(6)]
ceiling = max(means)
# Retain the unavoidable seven-window loss, but set the potential range to zero.
# (1099800 + 7*mu + rho)/(4200 + mu) < 235 requires 228*mu > 112800 + rho.
required = Fraction(112800, 228)
out = dict(scope='Upper ceiling on the achievable minimum for fixed centre weights in the specified six-feature relaxation, from a saved cycle only. No realizability claim.',
           cycle_length=len(rows), simplex_vertex_means=list(map(str, means)),
           normalized_ceiling=str(ceiling / 120),
           integer_weight_threshold_to_exclude_235_with_zero_potential_range=str(required),
           weighting_alone_cannot_exclude_235=ceiling <= required,
           rows=rows)
(HERE / 'data/weighted-ceiling.json').write_text(json.dumps(out, indent=2) + '\n')
print({k:v for k,v in out.items() if k != 'rows'})
