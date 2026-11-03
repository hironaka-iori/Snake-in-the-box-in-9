import CanonicalExclusions
import JointCountBridge
import LocalWindowTags

/-! Transfer of an explicit local pair-sum contradiction to actual snake counts. -/
namespace Snake9.PairGeometry113
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79
set_option maxHeartbeats 2000000

theorem actual_pair_sum
    (hlocal : ∀ S E : Nat → Bool,
      Axioms S E (winOf [0,1,2,0,3,4])
        (centresOf (winOf [0,1,2,0,3,4]) [(0,21),(0,5),(0,4),(0,5),(0,21)]) →
      absentCorners S 1 0 1 + absentCorners S 14 3 4 ≤ 8 → False)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,4])
    (hleft : coreAlpha p (r+2) ≤ 5)
    (hmiddle : coreAlpha p (r+3) ≤ 4)
    (hright : coreAlpha p (r+4) ≤ 5) :
    9 ≤ coreAlpha p (r+1)+coreAlpha p (r+5) := by
  obtain ⟨u, hu, hu9, hulen, hcs⟩ := actual_canonical_frame p r 6 hr
  have hsp := mkPerm_spec hu hu9 hulen
  have hP : ∀ j, j < 6 →
      (mkPerm u).fwd (dir p (r+j)) = ([0,1,2,0,3,4] : List Nat).getD j 0 := by
    intro j hj
    obtain ⟨hi, hd⟩ := hcs j hj
    rw [hshape] at hi hd
    rw [← hd]
    exact hsp _ hi
  have hc : Canon (winOf [0,1,2,0,3,4]) [0,1,2,0,3,4] := canon_winOf _
  have hb : ∀ i, i < ([(0,21),(0,5),(0,4),(0,5),(0,21)] : List (Nat × Nat)).length →
      (([(0,21),(0,5),(0,4),(0,5),(0,21)] : List (Nat × Nat)).getD i (0,21)).1 ≤
        coreAlpha p (r+i+1) ∧ coreAlpha p (r+i+1) ≤
      (([(0,21),(0,5),(0,4),(0,5),(0,21)] : List (Nat × Nat)).getD i (0,21)).2 := by
    intro i hi
    change i < 5 at hi
    have upper := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp_all [Nat.add_assoc]
  have ax := frame_axioms p (mkPerm u) r hc (by decide) hr hP hb
  have h1 := JointTags.frame_count p (mkPerm u) r hc hr hP 0 (by decide)
  have h5 := JointTags.frame_count p (mkPerm u) r hc hr hP 4 (by decide)
  have hw : winOf [0,1,2,0,3,4] = [0,1,3,7,6,14,30] := by decide +kernel
  have hd : dirOfStep 0 1 = 0 ∧ dirOfStep 1 3 = 1 ∧ dirOfStep 3 7 = 2 ∧
      dirOfStep 7 6 = 0 ∧ dirOfStep 6 14 = 3 ∧ dirOfStep 14 30 = 4 := by
    simp only [Tags.dirOfStep_eq]
    decide +kernel
  norm_num [hw, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    hd.2.2.2.2.1, hd.2.2.2.2.2, Nat.add_assoc] at h1 h5
  by_contra hsmall
  apply hlocal _ _ ax
  rw [h1,h5]
  omega

#print axioms actual_pair_sum
end Snake9.PairGeometry113
