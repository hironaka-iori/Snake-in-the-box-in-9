import CanonicalExclusions
import JointCountBridge
import JointCountTags
import SumCountSemantics112

namespace Snake9.ActualTriple129
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.LocalWindow.Tags

set_option maxHeartbeats 2000000

theorem actual_normalized_frame {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4]) :
    ∃ P : CPerm, ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0 := by
  obtain ⟨u,hu,hu9,huLen,hcs⟩ := actual_canonical_frame p r 7 hr
  have hsp := mkPerm_spec hu hu9 huLen
  refine ⟨mkPerm u,?_⟩
  intro j hj
  obtain ⟨hi,hd⟩ := hcs j hj
  rw [hshape] at hi hd
  rw [← hd]
  exact hsp _ hi

theorem actual_window_axioms {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0)
    (hfourth : coreAlpha p (r+4) = 3) :
    Axioms (sel p (amap P (vx p r))) (frameE p P (vx p r))
      (winOf [0,1,2,0,3,2,4]) (centresOf (winOf [0,1,2,0,3,2,4])
        [(0,21),(0,21),(0,21),(3,3),(0,21),(0,21)]) := by
  have hc : Canon (winOf [0,1,2,0,3,2,4]) [0,1,2,0,3,2,4] := canon_winOf _
  apply frame_axioms p P r hc (by decide) hr hP
  intro i hi
  change i < 6 at hi
  have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
  interval_cases i <;> simp_all [Nat.add_assoc]

theorem actual_three_counter_good {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0)
    (htriple : coreAlpha p (r+3)+coreAlpha p (r+5)+coreAlpha p (r+6) ≤ 11)
    (E : Nat → Bool) (M : MT) (ct : Ctr)
    (hneg : ct.lits.all (negP M) = true)
    (hperm : (ct.lits.map (vl M)).Perm
      (([⟨7,2,0,0,21⟩,⟨14,3,2,0,21⟩,⟨10,2,4,0,21⟩] : List Centre).flatMap corners))
    (hk : ct.k = 11) :
    JointTags.Good (sel p (amap P (vx p r))) E M ct := by
  constructor
  · apply List.all_eq_true.2
    intro x hx
    have hn := List.all_eq_true.1 hneg x hx
    simp only [negP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
    simp [baseOK, hn.1.2, hn.2]
  · have hc : Canon (winOf [0,1,2,0,3,2,4]) [0,1,2,0,3,2,4] := canon_winOf _
    have h3 := JointTags.frame_count p P r hc hr hP 2 (by decide)
    have h5 := JointTags.frame_count p P r hc hr hP 4 (by decide)
    have h6 := JointTags.frame_count p P r hc hr hP 5 (by decide)
    have hw : winOf [0,1,2,0,3,2,4] = [0,1,3,7,6,14,10,26] := by decide +kernel
    have hd : dirOfStep 3 7 = 2 ∧ dirOfStep 7 6 = 0 ∧ dirOfStep 6 14 = 3 ∧
        dirOfStep 14 10 = 2 ∧ dirOfStep 10 26 = 4 := by
      simp only [Tags.dirOfStep_eq]
      decide +kernel
    norm_num [hw,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2,Nat.add_assoc] at h3 h5 h6
    have hcount := SumCountSemantics112.countP_permuted_corners
      (sel p (amap P (vx p r))) E M ct.lits _ hneg hperm
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hcount
    rw [h3,h5,h6] at hcount
    rw [hcount,hk]
    simpa only [Nat.add_assoc] using htriple

#print axioms actual_normalized_frame
#print axioms actual_window_axioms
#print axioms actual_three_counter_good
end Snake9.ActualTriple129
