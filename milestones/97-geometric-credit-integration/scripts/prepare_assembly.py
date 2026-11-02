"""Generate the complete505-direction assembly; checking remains separate."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1]
plan=json.loads((HERE/'data/generation.json').read_text())
lines=['import GeometricTransport97',*['import '+r['module'] for r in plan['dispatch']],'','namespace Snake9.GeometricCredit97','open Snake9.LocalWindow Snake9.CreditTransport95 Snake9.Direction77','open Snake9.GraphWalk78 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95','set_option maxRecDepth 100000','set_option maxHeartbeats 2000000','','theorem geometric_catalogue_valid (i : Nat) (hi : i < 505) :','    LocalNineShare (extensions.getD i []) (geometricCredits.getD i 0) := by']
for j,row in enumerate(plan['dispatch']):
    if j+1<len(plan['dispatch']):
        lines += [f'  by_cases h{j} : i < {row["stop"]}',f'  · exact valid_{j:02d} i (by omega) h{j}']
    else:lines += [f'  exact valid_{j:02d} i (by omega) hi']
lines += ['','theorem actual_geometric_credit {m : Nat} (p : Snake m) (r : Nat)',
 '    (hr : r+9 ≤ m) :',
 '    geometricCredits.getD (directionId p r) 0 ≤',
 '      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=',
 '  actual_geometric_credit_from_catalogue geometric_catalogue_valid p r hr','',
 'theorem actual_geometric_history_credit {m : Nat} (p : Snake m) (r : Nat)',
 '    (hr : r+9 ≤ m) :',
 '    max (geometricCredits.getD (directionId p r) 0)',
 '      (historyCredit concreteRules (actualHistory p r) (directionId p r) (sixCode p r)) ≤',
 '      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=',
 '  actual_geometric_history_credit_from_catalogue geometric_catalogue_valid p r hr','',
 'theorem actual_geometric_history_weight {m : Nat} (p : Snake m) (r : Nat)',
 '    (hr : r+9 ≤ m) :',
 '    120 * (sixCode p r % 6 + 1) +',
 '      max (geometricCredits.getD (directionId p r) 0)',
 '        (historyCredit concreteRules (actualHistory p r) (directionId p r) (sixCode p r)) ≤',
 '      120 * coreAlpha p (r+8) +',
 '        ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=',
 '  actual_geometric_history_weight_from_catalogue geometric_catalogue_valid p r hr','',
 '#print axioms geometric_catalogue_valid','#print axioms actual_geometric_credit',
 '#print axioms actual_geometric_history_credit','#print axioms actual_geometric_history_weight',
 'end Snake9.GeometricCredit97']
p=HERE/'lean/GeometricAssembly97.lean';p.write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n')
order=['GeometricData97','Port97M59GeometryBatch00','GeometricTransport97']
order += [r['module'] for r in plan['ports'] if r['module'] not in order]
order += [r['module'] for r in plan['dispatch']]+['GeometricAssembly97']
if (HERE/'lean/SymbolCredit97.lean').exists():order.append('SymbolCredit97')
if (HERE/'lean/PressureArithmetic97.lean').exists():order.append('PressureArithmetic97')
sources={p.stem:hashlib.sha256(p.read_bytes()).hexdigest() for p in (HERE/'lean').glob('*.lean')}
assert set(order)==set(sources)
(HERE/'data/compile-order.json').write_text(json.dumps(dict(status='GENERATED_NOT_CHECKED',modules=order,source_sha256=sources),indent=2)+'\n')
print('ASSEMBLY_GENERATED',len(order),'modules')
