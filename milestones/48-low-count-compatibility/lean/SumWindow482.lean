import LocalWindowSat.JointIntervening482
import LocalWindowUnsat.JointIntervening482
import JointCountBridge
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.JointIntervening482
set_option maxHeartbeats 0

theorem local_sum_excluded (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ 5) : False := by
  obtain ⟨τ,hτ⟩ := sat S E ax h
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := [0, 1, 2, 3, 0, 4, 1, 0]

theorem sum_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j < 8 → P.fwd (dir p (r+j)) = directions.getD j 0) :
    6 ≤ coreAlpha p (r+4) + coreAlpha p (r+7) := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2 := by
    intro i hi
    have hiN : i < 7 := by simpa [bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simpa [bounds] using hu
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  have h4 := JointTags.frame_count p P r hc hr hP 3 (by decide)
  have c4v : window.getD 4 0 = centre4.v := by decide +kernel
  have c4a : dirOfStep (window.getD 3 0) (window.getD 4 0) = centre4.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c4b : dirOfStep (window.getD 4 0) (window.getD 5 0) = centre4.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c4a,c4b,c4v] at h4
  rw [show r+3+1 = r+4 by omega] at h4
  have h7 := JointTags.frame_count p P r hc hr hP 6 (by decide)
  have c7v : window.getD 7 0 = centre7.v := by decide +kernel
  have c7a : dirOfStep (window.getD 6 0) (window.getD 7 0) = centre7.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c7b : dirOfStep (window.getD 7 0) (window.getD 8 0) = centre7.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c7a,c7b,c7v] at h7
  rw [show r+6+1 = r+7 by omega] at h7
  by_contra! h
  apply local_sum_excluded _ _ ax
  unfold jointSum
  rw [h4,h7]
  omega

theorem low_count_sum {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,a,e,b,a] : List Nat).getD j 0) :
    6 ≤ coreAlpha p (r+4) + coreAlpha p (r+7) := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply sum_in_snake p (mkPerm [a,b,c,d,e]) r hr
  intro j hj
  rw [hd j hj]
  interval_cases j
  · exact hs 0 (by simp)
  · exact hs 1 (by simp)
  · exact hs 2 (by simp)
  · exact hs 3 (by simp)
  · exact hs 0 (by simp)
  · exact hs 4 (by simp)
  · exact hs 1 (by simp)
  · exact hs 0 (by simp)

#print axioms local_sum_excluded
#print axioms sum_in_snake
#print axioms low_count_sum
end Snake9.LocalWindow.JointIntervening482
