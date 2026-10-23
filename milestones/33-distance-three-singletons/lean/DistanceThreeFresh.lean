import LocalWindowSat.DistanceThree1
import LocalWindowUnsat.DistanceThree1
import JointCountBridge
import LocalWindowDirBridge

namespace Snake9.LocalWindow.DistanceThree1

theorem local_sum_excluded (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ 8) : False := by
  obtain ⟨τ, hτ⟩ := sat S E ax h
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := [0, 1, 2, 3, 4, 1, 5]

theorem high_sum_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) = directions.getD j 0)
 :
    9 ≤ coreAlpha p (r+1) + coreAlpha p (r+6) := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2 := by
    intro i hi
    have hi6 : i < 6 := by simpa [bounds] using hi
    have hg : bounds.getD i (0,21) = (0,21) := by
      interval_cases i <;> decide +kernel
    rw [hg]
    exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by omega)⟩
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  have h0 := JointTags.frame_count p P r hc hr hP 0 (by decide)
  have h5 := JointTags.frame_count p P r hc hr hP 5 (by decide)
  have a0 : window.getD 1 0 = centreA.v := by decide +kernel
  have a1 : dirOfStep (window.getD 0 0) (window.getD 1 0) = centreA.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have a2 : dirOfStep (window.getD 1 0) (window.getD 2 0) = centreA.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have b0 : window.getD 6 0 = centreB.v := by decide +kernel
  have b1 : dirOfStep (window.getD 5 0) (window.getD 6 0) = centreB.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have b2 : dirOfStep (window.getD 6 0) (window.getD 7 0) = centreB.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [a1, a2, a0] at h0
  rw [b1, b2, b0] at h5
  simp only [Nat.add_zero] at h0
  rw [show r+5+1 = r+6 by omega] at h5
  by_contra! h
  apply local_sum_excluded _ _ ax
  unfold jointSum
  rw [h0,h5]
  omega

/-- The coordinate labels need only be distinct valid cube coordinates. -/
theorem pattern_sum_in_snake {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x < 9)
    (hr : r+7 ≤ m)
    (hd : ∀ j, j < 7 → dir p (r+j) = ([a,b,c,d,e,b,f] : List Nat).getD j 0) :
    9 ≤ coreAlpha p (r+1) + coreAlpha p (r+6) := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply high_sum_in_snake p (mkPerm [a,b,c,d,e,f]) r hr
  intro j hj
  rw [hd j hj]
  interval_cases j
  · exact hs 0 (by simp)
  · exact hs 1 (by simp)
  · exact hs 2 (by simp)
  · exact hs 3 (by simp)
  · exact hs 4 (by simp)
  · exact hs 1 (by simp)
  · exact hs 5 (by simp)

#print axioms pattern_sum_in_snake
#print axioms local_sum_excluded
#print axioms high_sum_in_snake
end Snake9.LocalWindow.DistanceThree1
