"""Generate two full-context benchmarks with the exact original inequalities."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
specs=[dict(module='CompletedContext100',profile='Completed',floor='completedCredit',P=483,di=35,q=0,cls=25,root=2620),
       dict(module='ConditionalContext100',profile='Conditional',floor='conditionalCredit',P=496,di=177,q=43,cls=85,root=3690)]
for s in specs:
    p=s['profile'];floor=s['floor'];P=s['P'];d=s['di'];q=s['q'];cls=s['cls'];root=s['root']
    src=f'''import PrefixChecker100
import {p}Potential99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates100
open Snake9.PrefixChecker100 Snake9.PotentialChecker99 Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92

theorem {p.lower()}_prefix :
    checkPrefix (fun code => decide
      ({P}+{p}.potential (edgeTarget {q} {d} code) ≤
        weight {floor} {q} {d} code+{p}.potential (edgeSource {q} {d} code)))
      6 0 {root} = true := by decide +kernel

theorem {p.lower()}_context :
    contextCheck (weight {floor}) {P} {p}.potential {d} {q} = true := by
  apply contextCheck_of_prefix (weight {floor}) {P} {p}.potential {d} {q} {cls}
  · decide +kernel
  · exact {p.lower()}_prefix

#print axioms {p.lower()}_prefix
#print axioms {p.lower()}_context
end Snake9.PrefixCertificates100
'''
    (HERE/'lean'/f"{s['module']}.lean").write_text(src)
(HERE/'data/contexts.json').write_text(json.dumps(specs,indent=2)+'\n')
print('GENERATED_TWO_COMPLETE_CONTEXTS')
