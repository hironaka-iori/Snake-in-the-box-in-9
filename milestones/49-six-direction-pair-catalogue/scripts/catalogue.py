"""Derive every negative survey row from the shortened basis, in Lean."""
from pathlib import Path
import json
from survey import canon
HERE=Path(__file__).resolve().parents[1]
cases=json.loads((HERE/'data/cases.json').read_text());rows=json.loads((HERE/'data/survey.json').read_text())
s='\n'.join(f'import PairBasis{c["number"]}' for c in cases)+'\nnamespace Snake9.LocalWindow.SurveyCatalogue\nset_option maxHeartbeats 0\n'
coverage=[]
for row in rows:
 if row['status']!='UNSAT':continue
 match=None
 for c in cases:
  L=len(c['dirs'])
  for start in range(7-L):
   if list(canon(row['dirs'][start:start+L]))!=c['dirs']:continue
   if [start+j for j in c['positions']]!=row['positions']:continue
   if not all(a<=b for a,b in zip(row['caps'],c['caps'])):continue
   match=c,start;break
  if match:break
 assert match,row
 c,start=match;L=len(c['dirs']);n=c['number'];letter='abcdef'[:max(row['dirs'])+1];labels=','.join(letter);named=','.join(letter[d] for d in row['dirs']);coords=list(dict.fromkeys(row['dirs'][start:start+L]));args=' '.join(letter[d] for d in coords);sublabels=','.join(letter[d] for d in coords)
 name=row['name'].replace('-','_');j,k=row['positions'];u,v=row['caps']
 coverage.append(dict(row=row['name'],basis=n,start=start,labels=coords,theorem=name))
 s+=f'''
theorem {name} {{m : Nat}} (p : Snake m) (r {' '.join(letter)} : Nat)
    (hn : [{labels}].Nodup) (h9 : ∀ x ∈ [{labels}], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([{named}] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+{j}) ≤ {u}) (hsecond : coreAlpha p (r+{k}) ≤ {v}) : False := by
  apply PairBasis{n}.exclusion p (r+{start}) {args}
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
'''
 for t in range(L):s+=f'    · simpa [Nat.add_assoc] using hd {start+t} (by decide)\n'
 for orig,cap,h in [(j,c['caps'][0],'hfirst'),(k,c['caps'][1],'hsecond')]:
  s+=f'''  · have hbound : coreAlpha p (r+{orig}) ≤ {cap} := by omega
    simpa [Nat.add_assoc] using hbound
'''
 s+=f'#print axioms {name}\n'
s+='end Snake9.LocalWindow.SurveyCatalogue\n'
(HERE/'lean/SurveyCatalogue.lean').write_text(s,encoding='utf-8')
(HERE/'data/coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
print('Generated',len(coverage),'survey deductions')
