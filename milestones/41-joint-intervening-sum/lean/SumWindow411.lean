import LocalWindowSat.JointIntervening411
import LocalWindowUnsat.JointIntervening411
import JointCountBridge
import LocalWindowDirBridge

namespace Snake9.LocalWindow.JointIntervening411
set_option maxHeartbeats 0

theorem local_sum_excluded (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ 11) : False := by
  obtain ⟨τ,hτ⟩ := sat S E ax h
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := [0, 1, 2, 3, 4, 2, 0, 3]

theorem sum_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j < 8 → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) : 12 ≤ coreAlpha p (r+3) + coreAlpha p (r+6) := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  have h3 := JointTags.frame_count p P r hc hr hP 2 (by decide)
  have c3v : window.getD 3 0 = centre3.v := by decide +kernel
  have c3a : dirOfStep (window.getD 2 0) (window.getD 3 0) = centre3.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c3b : dirOfStep (window.getD 3 0) (window.getD 4 0) = centre3.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c3a,c3b,c3v] at h3
  rw [show r+2+1 = r+3 by omega] at h3
  have h6 := JointTags.frame_count p P r hc hr hP 5 (by decide)
  have c6v : window.getD 6 0 = centre6.v := by decide +kernel
  have c6a : dirOfStep (window.getD 5 0) (window.getD 6 0) = centre6.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c6b : dirOfStep (window.getD 6 0) (window.getD 7 0) = centre6.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c6a,c6b,c6v] at h6
  rw [show r+5+1 = r+6 by omega] at h6
  by_contra! h
  apply local_sum_excluded _ _ ax
  unfold jointSum
  rw [h3,h6]
  omega

theorem joint_intervening_sum {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) (h7 : coreAlpha p (r+7) ≤ 3) :
    12 ≤ coreAlpha p (r+3) + coreAlpha p (r+6) := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply sum_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    rw [hd j hj]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 4 (by simp)
    · exact hs 2 (by simp)
    · exact hs 0 (by simp)
    · exact hs 3 (by simp)
  · intro i hi
    have hi7 : i < 7 := by simpa [bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

#print axioms local_sum_excluded
#print axioms sum_in_snake
#print axioms joint_intervening_sum
end Snake9.LocalWindow.JointIntervening411
