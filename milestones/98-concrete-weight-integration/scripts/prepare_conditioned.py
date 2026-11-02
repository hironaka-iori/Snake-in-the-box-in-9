"""Generate the five closed count-conditioned credits and exact-key transfer."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
rules=[('513',[0,1,2,3,1,4],[3,3,3,6,5],47,'SharePressure513','refuted_share'),
       ('520',[0,1,2,3,4,5],[3,6,2,3,6],95,'SharePressure520','refuted_share'),
       ('530',[0,1,2,0,3,4],[6,3,6,3,3],95,'ShareObstruction530','refuted_share'),
       ('535',[0,1,2,3,4,5],[4,6,2,3,6],95,'ShareObstruction535','refuted_share'),
       ('120',[0,1,2,3,4,5],[4,5,4,2,6],119,'ShareWindow120','refuted')]
L=['import CombinedEnvironment98','','namespace Snake9.Conditioned98',
   'open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow',
   'open Snake9.GraphWalk78 Snake9.Direction77 Snake9.SymbolCredit97',
   'open Snake9.GraphInterpretation75','',
   'set_option maxHeartbeats 2000000','set_option maxRecDepth 100000','',
   '/-- A stored suffix matches a rule in either orientation; both lists reverse. -/',
   'def ruleCredit (cs syms : List Nat) (cap di code : Nat) : Nat :=',
   '  if (canon ((extensions.getD di []).drop 3) = cs ∧ code % 7776 = encodeCounts syms 0) ∨',
   '     (canon (((extensions.getD di []).drop 3).reverse) = cs ∧',
   '       code % 7776 = encodeCounts syms.reverse 0) then cap+1 else 0','',
   'theorem rule_credit_bound (cs syms : List Nat) (cap : Nat)',
   '    (hlen : syms.length = 5) (hvalid : ∀ x ∈ syms, 1 ≤ x ∧ x ≤ 6)',
   '    (href : RefutedShare (winOf cs) (boundsOf syms) 12 cap)',
   '    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :',
   '    ruleCredit cs syms cap (directionId p r) (sixCode p r) ≤',
   '      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by',
   '  unfold ruleCredit',
   '  split_ifs with h',
   '  · rw [direction_decode p r hr] at h',
   '    rcases h with ⟨hs,hc⟩ | ⟨hs,hc⟩',
   '    · exact encoded_forward_suffix_share p r cs syms hr hlen hvalid href hs hc',
   '    · exact encoded_reversed_suffix_share p r cs syms hr hlen hvalid href hs hc',
   '  · exact Nat.zero_le _','']
for name,cs,syms,cap,ns,thm in rules:
    L += [f'theorem refuted{name} : RefutedShare (winOf {cs}) (boundsOf {syms}) 12 {cap} := by',
          f'  have hw : winOf {cs} = {ns}.window := by decide +kernel',
          f'  have hb : boundsOf {syms} = {ns}.bounds := by decide +kernel',
          f'  simpa only [hw, hb, {ns}.resolution, {ns}.cap] using {ns}.{thm}','']
terms=[f'ruleCredit {cs} {syms} {cap} di code' for _,cs,syms,cap,_,_ in rules]
expr=terms[-1]
for term in reversed(terms[:-1]):expr=f'max ({term}) ({expr})'
L += ['def conditionedCredit (di code : Nat) : Nat :=', '  '+expr,'',
      'theorem actual_conditioned_credit {m : Nat} (p : Snake m) (r : Nat)',
      '    (hr : r+9 ≤ m) : conditionedCredit (directionId p r) (sixCode p r) ≤',
      '      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by',
      '  unfold conditionedCredit']
for i,(name,cs,syms,cap,_,_) in enumerate(rules):
    if i<len(rules)-1:
        L += ['  apply max_le','  · exact rule_credit_bound '+f'{cs} {syms} {cap}',
              f'      (by decide +kernel) (by decide +kernel) refuted{name} p r hr']
    else:
        L += [f'  exact rule_credit_bound {cs} {syms} {cap}',
              f'    (by decide +kernel) (by decide +kernel) refuted{name} p r hr']
L+=['','#print axioms rule_credit_bound']
L += [f'#print axioms refuted{name}' for name,*_ in rules]
L += ['#print axioms actual_conditioned_credit','end Snake9.Conditioned98']
(HERE/'lean/CountConditionedCredits98.lean').write_text('\n'.join(L)+'\n',encoding='utf-8',newline='\n')
(HERE/'data/conditioned-rules.json').write_text(json.dumps([dict(name=n,directions=d,symbols=s,cap=c,credit=c+1,namespace=ns,theorem=t) for n,d,s,c,ns,t in rules],indent=2)+'\n')
print('GENERATED_FIVE_CONDITIONED_CREDITS')
