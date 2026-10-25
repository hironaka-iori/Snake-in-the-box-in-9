"""Generate arbitrary-coordinate statements for the low-count restrictions."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
cases=[]
for n in [481,482,483]:
    kind='sum' if n<483 else 'cycle'
    m=json.loads((HERE/f'data/{kind}{n}.json').read_text())
    cases.append(dict(number=n,kind=kind,dirs=m['dirs'],bounds=m['bounds'],positions=m.get('positions',[1,5]),cap=m.get('joint_cap'),caps=None if kind=='sum' else [3,2]))
(HERE/'data/cases.json').write_text(json.dumps(cases,indent=2)+'\n')
for case in cases[:2]:
    n=case['number'];ds=case['dirs'];L=len(ds);pos=case['positions'];cap=case['cap'];letters='abcde'[:max(ds)+1];labels=','.join(letters);named=','.join(letters[d] for d in ds)
    s=f'''import LocalWindowSat.JointIntervening{n}
import LocalWindowUnsat.JointIntervening{n}
import JointCountBridge
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.JointIntervening{n}
set_option maxHeartbeats 0

theorem local_sum_excluded (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ {cap}) : False := by
  obtain ⟨τ,hτ⟩ := sat S E ax h
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := {ds}

theorem sum_in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+{L} ≤ m)
    (hP : ∀ j, j < {L} → P.fwd (dir p (r+j)) = directions.getD j 0) :
    {cap+1} ≤ coreAlpha p (r+{pos[0]}) + coreAlpha p (r+{pos[1]}) := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2 := by
    intro i hi
    have hiN : i < {L-1} := by simpa [bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simpa [bounds] using hu
  have ax := frame_axioms p P r hc (by decide) hr hP hb
'''
    for j in pos:
        s+=f'''  have h{j} := JointTags.frame_count p P r hc hr hP {j-1} (by decide)
  have c{j}v : window.getD {j} 0 = centre{j}.v := by decide +kernel
  have c{j}a : dirOfStep (window.getD {j-1} 0) (window.getD {j} 0) = centre{j}.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c{j}b : dirOfStep (window.getD {j} 0) (window.getD {j+1} 0) = centre{j}.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c{j}a,c{j}b,c{j}v] at h{j}
  rw [show r+{j-1}+1 = r+{j} by omega] at h{j}
'''
    s+=f'''  by_contra! h
  apply local_sum_excluded _ _ ax
  unfold jointSum
  rw [h{pos[0]},h{pos[1]}]
  omega

theorem low_count_sum {{m : Nat}} (p : Snake m) (r {' '.join(letters)} : Nat)
    (hn : [{labels}].Nodup) (h9 : ∀ x ∈ [{labels}], x < 9)
    (hr : r+{L} ≤ m)
    (hd : ∀ j, j < {L} → dir p (r+j) = ([{named}] : List Nat).getD j 0) :
    {cap+1} ≤ coreAlpha p (r+{pos[0]}) + coreAlpha p (r+{pos[1]}) := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply sum_in_snake p (mkPerm [{labels}]) r hr
  intro j hj
  rw [hd j hj]
  interval_cases j
'''+''.join(f'  · exact hs {d} (by simp)\n' for d in ds)+f'''
#print axioms local_sum_excluded
#print axioms sum_in_snake
#print axioms low_count_sum
end Snake9.LocalWindow.JointIntervening{n}
'''
    (HERE/f'lean/SumWindow{n}.lean').write_text(s,encoding='utf-8')
s='''import CycleExclusion483
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.LowCountCompatibility
set_option maxHeartbeats 0

theorem asymmetric_exclusion {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,c] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) (h5 : coreAlpha p (r+5) ≤ 2) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow483.excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hjL : j<6 := by simpa [CycleWindow483.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 4 (by simp)
    · exact hs 2 (by simp)
  · intro i hi
    have hiN : i<5 := by simpa [CycleWindow483.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow483.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem conditional_lower {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,c] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) : 3 ≤ coreAlpha p (r+5) := by
  by_contra h
  exact asymmetric_exclusion p r a b c d e hn h9 hr hd h1 (by omega)
#print axioms asymmetric_exclusion
#print axioms conditional_lower
end Snake9.LocalWindow.LowCountCompatibility
'''
(HERE/'lean/LowCountCompatibility.lean').write_text(s,encoding='utf-8')
p=(ROOT/'milestones/47-critical-singleton-patterns/scripts/replay.py').read_text()
p=p.replace("[('45-pair-endpoint-demand'","[('47-critical-singleton-patterns','latest'),('45-pair-endpoint-demand'")
p=p.replace('for number in [471,472,473]:', 'for number in [481,482,483]:').replace("mod=f'CycleWindow{number}'", "mod=f'JointIntervening{number}' if number<483 else f'CycleWindow{number}'")
p=p.replace("names+=['LocalWindowUnsat/'+mod,f'CycleExclusion{number}']", "names+=['LocalWindowUnsat/'+mod, f'SumWindow{number}' if number<483 else f'CycleExclusion{number}']")
p=p.replace("if (HERE/'lean/SingletonPatterns.lean').exists():names+=['SingletonPatterns']", "names+=['LowCountCompatibility']")
(HERE/'scripts/replay.py').write_text(p,encoding='utf-8')
