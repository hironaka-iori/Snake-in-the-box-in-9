import LocalWindowSat.JointSum2
import LocalWindowUnsat.JointSum2
import JointCountBridge

namespace Snake9.LocalWindow.JointSum2

theorem local_sum_excluded (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ 28) : False := by
  obtain ⟨τ, hτ⟩ := sat S E ax h
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := [0, 1, 2, 3, 4, 1, 2, 0]

theorem high_sum_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j < 8 → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) :
    29 ≤ coreAlpha p (r+1) + coreAlpha p (r+4) + coreAlpha p (r+7) := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  have h0 := JointTags.frame_count p P r hc hr hP 0 (by decide)
  have h3 := JointTags.frame_count p P r hc hr hP 3 (by decide)
  have h6 := JointTags.frame_count p P r hc hr hP 6 (by decide)
  have a0 : window.getD 1 0 = centreA.v := by decide +kernel
  have a1 : dirOfStep (window.getD 0 0) (window.getD 1 0) = centreA.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have a2 : dirOfStep (window.getD 1 0) (window.getD 2 0) = centreA.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have b0 : window.getD 4 0 = centreB.v := by decide +kernel
  have b1 : dirOfStep (window.getD 3 0) (window.getD 4 0) = centreB.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have b2 : dirOfStep (window.getD 4 0) (window.getD 5 0) = centreB.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c0 : window.getD 7 0 = centreC.v := by decide +kernel
  have c1 : dirOfStep (window.getD 6 0) (window.getD 7 0) = centreC.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c2 : dirOfStep (window.getD 7 0) (window.getD 8 0) = centreC.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [a1, a2, a0] at h0
  rw [b1, b2, b0] at h3
  rw [c1, c2, c0] at h6
  simp only [Nat.add_zero] at h0
  rw [show r+3+1 = r+4 by omega] at h3
  rw [show r+6+1 = r+7 by omega] at h6
  by_contra! h
  apply local_sum_excluded _ _ ax
  unfold jointSum
  rw [h0,h3,h6]
  omega

#print axioms local_sum_excluded
#print axioms high_sum_in_snake
end Snake9.LocalWindow.JointSum2
