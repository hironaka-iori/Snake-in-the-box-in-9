from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/187-clause-interpretation')
source=r'''import BoundarySlack187
namespace Combined187

theorem five_slack_requires_small_loss (m W L : Nat) (hm : 234 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (ht : 520*(m-7) ≤ W+1023) : L ≤ 31 := by omega

theorem five_slack_with_loss (m W L : Nat) (hm : 7 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (ht : 520*(m-7) ≤ W+1023)
    (hloss : 234 ≤ m → 32 ≤ L) : m ≤ 233 := by
  by_contra h
  have hlarge : 234 ≤ m := by omega
  have := five_slack_requires_small_loss m W L hlarge hb ht
  have := hloss hlarge
  omega

theorem four_slack_only_at_small_loss (m W L : Nat) (hm : 7 ≤ m)
    (hb5 : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (hb4 : L ≤ 31 → W+4200*m+5*L ≤ 1098840+4*(m-7))
    (ht : 520*(m-7) ≤ W+1023) : m ≤ 233 := by
  by_contra h
  have hlarge : 234 ≤ m := by omega
  have hl := five_slack_requires_small_loss m W L hlarge hb5 ht
  have := (four_point_slack m W L hm (hb4 hl) ht).2
  omega

#print axioms five_slack_requires_small_loss
#print axioms five_slack_with_loss
#print axioms four_slack_only_at_small_loss
end Combined187
'''
name='BoundarySlackCases187'
p=H/'lean'/(name+'.lean');assert not p.exists();p.write_text(source,encoding='utf-8',newline='\n')
base=json.loads((H/'data/BoundarySlack187-execution.json').read_text())
base['new_module_order'].append(name)
base['source_sha256'][name]=hashlib.sha256(p.read_bytes()).hexdigest()
(H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
p=H/'data/current-order.json';order=json.loads(p.read_text());order.insert(2,name)
p.write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/prepare_loss_case.py').write_bytes(Path(__file__).read_bytes())
print('Prepared the low-loss case split; awaiting sequential Lean check.')
