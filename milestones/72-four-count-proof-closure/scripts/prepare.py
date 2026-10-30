"""Keep maximal interval exclusions and generate arbitrary-label wrappers."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
rows=json.loads((HERE/'data/probes.json').read_text())
assert len(rows)==16 and all(r['status'] in ('UNSAT','UNKNOWN') for r in rows)
def contains(a,b):
    return a['dirs']==b['dirs'] and all(al<=bl<=bh<=ah for (al,ah),(bl,bh) in zip(a['bounds'],b['bounds']))
maximal=[r for r in rows if not any(r!=s and contains(s,r) and not contains(r,s) for s in rows)]
cases=[dict(number=7201+r['basis_id'],kind='cycle',dirs=r['dirs'],bounds=r['bounds'],probe=r['name'],basis_id=r['basis_id'],probe_status=r['status']) for r in maximal]
stronger=HERE/'data/key-101-caps.json'
if stronger.exists():
    r=json.loads(stronger.read_text());assert r['status']=='UNSAT'
    cases.append(dict(number=7218,kind='cycle',dirs=r['dirs'],bounds=r['bounds'],probe=r['name'],basis_id=101,probe_status=r['status']))
strongest=HERE/'data/key-102-caps.json'
if strongest.exists():
    r=json.loads(strongest.read_text());assert r['status']=='UNSAT'
    cases.append(dict(number=7219,kind='cycle',dirs=r['dirs'],bounds=r['bounds'],probe=r['name'],basis_id=102,probe_status=r['status']))
(HERE/'data/cases.json').write_text(json.dumps(cases,indent=2)+'\n')
coverage=[]
for r in rows:
    target=dict(r,bounds=[[c,c] for c in r['counts']]);case=next(c for c in cases if contains(c,target))
    coverage.append(dict(basis_id=r['basis_id'],case=case['number'],dirs=r['dirs'],counts=r['counts']))
(HERE/'data/coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
for c in cases:
    n=c['number'];ds=c['dirs'];labels='a,b,c,d';named=','.join('abcd'[d] for d in ds)
    bs='['+','.join(f'({a},{b})' for a,b in c['bounds'])+']'
    text=f'''import CycleExclusion{n}
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.FourCount{n}
set_option maxHeartbeats 0

theorem exclusion {{m : Nat}} (p : Snake m) (r a b c d : Nat)
    (hn : [{labels}].Nodup) (h9 : ∀ x ∈ [{labels}], x<9)
    (hr : r+5 ≤ m)
    (hd : ∀ j, j<5 → dir p (r+j) = ([{named}] : List Nat).getD j 0)
    (hb : ∀ i, i<4 →
      (({bs} : List (Nat × Nat)).getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (({bs} : List (Nat × Nat)).getD i (0,21)).2) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow{n}.excluded_in_snake p (mkPerm [{labels}]) r hr
  · intro j hj
    have hjL : j<5 := by simpa [CycleWindow{n}.directions] using hj
    rw [hd j hjL]
    interval_cases j
'''+''.join(f'    · exact hs {d} (by simp)\n' for d in ds)+f'''  · intro i hi
    have hiL : i<4 := by simpa [CycleWindow{n}.bounds] using hi
    simpa [CycleWindow{n}.bounds] using hb i hiL
#print axioms exclusion
end Snake9.LocalWindow.FourCount{n}
'''
    (HERE/f'lean/FourCount{n}.lean').write_text(text,encoding='utf-8')
print('Prepared',len(cases),'interval certificates covering',len(coverage),'selected keys.')
