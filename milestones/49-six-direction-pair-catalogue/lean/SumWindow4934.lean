import LocalWindowSat.JointIntervening4934
import LocalWindowUnsat.JointIntervening4934
import JointCountBridge
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.JointIntervening4934
set_option maxHeartbeats 0

theorem local_sum_excluded (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ 4) : False := by
  obtain ⟨τ,hτ⟩ := sat S E ax h
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := [0, 1, 2, 0]

theorem sum_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+4 ≤ m)
    (hP : ∀ j, j < 4 → P.fwd (dir p (r+j)) = directions.getD j 0) :
    5 ≤ coreAlpha p (r+1) + coreAlpha p (r+3) := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2 := by
    intro i hi
    have hiN : i < 3 := by simpa [bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simpa [bounds] using hu
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  have h1 := JointTags.frame_count p P r hc hr hP 0 (by decide)
  have c1v : window.getD 1 0 = centre1.v := by decide +kernel
  have c1a : dirOfStep (window.getD 0 0) (window.getD 1 0) = centre1.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c1b : dirOfStep (window.getD 1 0) (window.getD 2 0) = centre1.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c1a,c1b,c1v] at h1
  rw [show r+0+1 = r+1 by omega] at h1
  have h3 := JointTags.frame_count p P r hc hr hP 2 (by decide)
  have c3v : window.getD 3 0 = centre3.v := by decide +kernel
  have c3a : dirOfStep (window.getD 2 0) (window.getD 3 0) = centre3.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c3b : dirOfStep (window.getD 3 0) (window.getD 4 0) = centre3.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c3a,c3b,c3v] at h3
  rw [show r+2+1 = r+3 by omega] at h3
  by_contra! h
  apply local_sum_excluded _ _ ax
  unfold jointSum
  rw [h1,h3]
  omega

theorem low_count_sum {m : Nat} (p : Snake m) (r a b c : Nat)
    (hn : [a,b,c].Nodup) (h9 : ∀ x ∈ [a,b,c], x < 9)
    (hr : r+4 ≤ m)
    (hd : ∀ j, j < 4 → dir p (r+j) = ([a,b,c,a] : List Nat).getD j 0) :
    5 ≤ coreAlpha p (r+1) + coreAlpha p (r+3) := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply sum_in_snake p (mkPerm [a,b,c]) r hr
  intro j hj
  rw [hd j hj]
  interval_cases j
  · exact hs 0 (by simp)
  · exact hs 1 (by simp)
  · exact hs 2 (by simp)
  · exact hs 0 (by simp)

#print axioms local_sum_excluded
#print axioms sum_in_snake
#print axioms low_count_sum
end Snake9.LocalWindow.JointIntervening4934
