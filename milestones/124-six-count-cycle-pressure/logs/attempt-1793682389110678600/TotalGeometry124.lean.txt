import CanonicalExclusions
import JointCountBridge
import LocalWindowTags

/-! Transfer of an explicit local total-count contradiction to actual snake counts. -/
namespace Snake9.TotalGeometry124
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79
set_option maxHeartbeats 2000000

theorem actual_total_sum
    (hlocal : ∀ S E : Nat → Bool,
      Axioms S E (winOf [0,1,2,3,0,4,1])
        (centresOf (winOf [0,1,2,3,0,4,1]) [(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)]) →
      absentCorners S 1 0 1 + absentCorners S 3 1 2 +
        absentCorners S 7 2 3 + absentCorners S 15 3 0 +
        absentCorners S 14 0 4 + absentCorners S 30 4 1 ≤ 24 → False)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,3,0,4,1]) :
    25 ≤ coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5)+coreAlpha p (r+6) := by
  obtain ⟨u, hu, hu9, hulen, hcs⟩ := actual_canonical_frame p r 7 hr
  have hsp := mkPerm_spec hu hu9 hulen
  have hP : ∀ j, j < 7 →
      (mkPerm u).fwd (dir p (r+j)) = ([0,1,2,3,0,4,1] : List Nat).getD j 0 := by
    intro j hj
    obtain ⟨hi, hd⟩ := hcs j hj
    rw [hshape] at hi hd
    rw [← hd]
    exact hsp _ hi
  have hc : Canon (winOf [0,1,2,3,0,4,1]) [0,1,2,3,0,4,1] := canon_winOf _
  have hb : ∀ i, i < ([(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)] : List (Nat × Nat)).length →
      (([(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)] : List (Nat × Nat)).getD i (0,21)).1 ≤
        coreAlpha p (r+i+1) ∧ coreAlpha p (r+i+1) ≤
      (([(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)] : List (Nat × Nat)).getD i (0,21)).2 := by
    intro i hi
    change i < 6 at hi
    have upper := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp_all [Nat.add_assoc]
  have ax := frame_axioms p (mkPerm u) r hc (by decide) hr hP hb
  have h1 := JointTags.frame_count p (mkPerm u) r hc hr hP 0 (by decide)
  have h2 := JointTags.frame_count p (mkPerm u) r hc hr hP 1 (by decide)
  have h3 := JointTags.frame_count p (mkPerm u) r hc hr hP 2 (by decide)
  have h4 := JointTags.frame_count p (mkPerm u) r hc hr hP 3 (by decide)
  have h5 := JointTags.frame_count p (mkPerm u) r hc hr hP 4 (by decide)
  have h6 := JointTags.frame_count p (mkPerm u) r hc hr hP 5 (by decide)
  have hw : winOf [0,1,2,3,0,4,1] = [0,1,3,7,15,14,30,28] := by decide +kernel
  have hd : dirOfStep 0 1 = 0 ∧ dirOfStep 1 3 = 1 ∧ dirOfStep 3 7 = 2 ∧
      dirOfStep 7 15 = 3 ∧ dirOfStep 15 14 = 0 ∧ dirOfStep 14 30 = 4 ∧ dirOfStep 30 28 = 1 := by
    simp only [Tags.dirOfStep_eq]
    decide +kernel
  norm_num [hw, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2, Nat.add_assoc] at h1 h2 h3 h4 h5 h6
  by_contra hsmall
  apply hlocal _ _ ax
  rw [h1,h2,h3,h4,h5,h6]
  omega

#print axioms actual_total_sum
end Snake9.TotalGeometry124
