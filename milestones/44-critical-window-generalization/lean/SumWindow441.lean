import LocalWindowSat.JointIntervening441
import LocalWindowUnsat.JointIntervening441
import JointCountBridge
import LocalWindowDirBridge

namespace Snake9.LocalWindow.JointIntervening441
set_option maxHeartbeats 0

theorem local_sum_excluded (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ 6) : False := by
  obtain ⟨τ,hτ⟩ := sat S E ax h
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := [0,1,2,3,4,0,3,1]

theorem sum_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j < 8 → P.fwd (dir p (r+j)) = directions.getD j 0) :
    7 ≤ coreAlpha p (r+2) + coreAlpha p (r+6) := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2 := by
    intro i hi
    have hi7 : i < 7 := by simpa [bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simpa [bounds] using hu
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  have h2 := JointTags.frame_count p P r hc hr hP 1 (by decide)
  have c2v : window.getD 2 0 = centre2.v := by decide +kernel
  have c2a : dirOfStep (window.getD 1 0) (window.getD 2 0) = centre2.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c2b : dirOfStep (window.getD 2 0) (window.getD 3 0) = centre2.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c2a,c2b,c2v] at h2
  rw [show r+1+1 = r+2 by omega] at h2
  have h6 := JointTags.frame_count p P r hc hr hP 5 (by decide)
  have c6v : window.getD 6 0 = centre6.v := by decide +kernel
  have c6a : dirOfStep (window.getD 5 0) (window.getD 6 0) = centre6.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c6b : dirOfStep (window.getD 6 0) (window.getD 7 0) = centre6.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c6a,c6b,c6v] at h6
  rw [show r+5+1 = r+6 by omega] at h6
  by_contra! h
  apply local_sum_excluded _ _ ax
  unfold jointSum
  rw [h2,h6]
  omega

theorem exterior_turn_sum {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,a,d,b] : List Nat).getD j 0) :
    7 ≤ coreAlpha p (r+2) + coreAlpha p (r+6) := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply sum_in_snake p (mkPerm [a,b,c,d,e]) r hr
  intro j hj
  rw [hd j hj]
  interval_cases j
  · exact hs 0 (by simp)
  · exact hs 1 (by simp)
  · exact hs 2 (by simp)
  · exact hs 3 (by simp)
  · exact hs 4 (by simp)
  · exact hs 0 (by simp)
  · exact hs 3 (by simp)
  · exact hs 1 (by simp)

#print axioms local_sum_excluded
#print axioms sum_in_snake
#print axioms exterior_turn_sum
end Snake9.LocalWindow.JointIntervening441
