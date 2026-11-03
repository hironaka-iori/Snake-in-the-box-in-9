import ActualSplit129
import JointCountBridge
import JointCountTags
import SumCountSemantics112

namespace Snake9.ActualCounters129
open Finset
open scoped BigOperators
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.LocalWindow.Tags

set_option maxHeartbeats 2000000

private theorem frame_counts {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0) :
    absentCorners (sel p (amap P (vx p r))) 1 0 1 = coreAlpha p (r+1) ∧
    absentCorners (sel p (amap P (vx p r))) 3 1 2 = coreAlpha p (r+2) ∧
    absentCorners (sel p (amap P (vx p r))) 7 2 0 = coreAlpha p (r+3) ∧
    absentCorners (sel p (amap P (vx p r))) 6 0 3 = coreAlpha p (r+4) ∧
    absentCorners (sel p (amap P (vx p r))) 14 3 2 = coreAlpha p (r+5) ∧
    absentCorners (sel p (amap P (vx p r))) 10 2 4 = coreAlpha p (r+6) := by
  have hc : Canon (winOf [0,1,2,0,3,2,4]) [0,1,2,0,3,2,4] := canon_winOf _
  have h1 := JointTags.frame_count p P r hc hr hP 0 (by decide)
  have h2 := JointTags.frame_count p P r hc hr hP 1 (by decide)
  have h3 := JointTags.frame_count p P r hc hr hP 2 (by decide)
  have h4 := JointTags.frame_count p P r hc hr hP 3 (by decide)
  have h5 := JointTags.frame_count p P r hc hr hP 4 (by decide)
  have h6 := JointTags.frame_count p P r hc hr hP 5 (by decide)
  have hw : winOf [0,1,2,0,3,2,4] = [0,1,3,7,6,14,10,26] := by decide +kernel
  have hd : dirOfStep 0 1 = 0 ∧ dirOfStep 1 3 = 1 ∧ dirOfStep 3 7 = 2 ∧
      dirOfStep 7 6 = 0 ∧ dirOfStep 6 14 = 3 ∧ dirOfStep 14 10 = 2 ∧
      dirOfStep 10 26 = 4 := by
    simp only [Tags.dirOfStep_eq]
    decide +kernel
  norm_num [hw, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2, Nat.add_assoc] at h1 h2 h3 h4 h5 h6
  exact ⟨h1,h2,h3,h4,h5,h6⟩

theorem actual_window_axioms {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0)
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22)
    (hfourth : coreAlpha p (r+4) = 3) :
    Axioms (sel p (amap P (vx p r))) (frameE p P (vx p r))
      (winOf [0,1,2,0,3,2,4]) (centresOf (winOf [0,1,2,0,3,2,4])
        [(1,21),(2,21),(1,21),(3,21),(1,21),(1,21)]) ∧
    Axioms (sel p (amap P (vx p r))) (frameE p P (vx p r))
      (winOf [0,1,2,0,3,2,4]) (centresOf (winOf [0,1,2,0,3,2,4])
        [(3,21),(5,21),(1,21),(3,3),(1,21),(1,21)]) := by
  have hc : Canon (winOf [0,1,2,0,3,2,4]) [0,1,2,0,3,2,4] := canon_winOf _
  constructor
  · exact frame_axioms p P r hc (by decide) hr hP
      (ActualBounds125.actual_six_bounds p r hr hshape htotal)
  · exact frame_axioms p P r hc (by decide) hr hP
      (ActualSplit129.actual_equality_bounds p r hr hshape htotal hfourth)

theorem actual_total_counter_good {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0)
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22)
    (E : Nat → Bool) (M : MT) (ct : Ctr)
    (hneg : ct.lits.all (negP M) = true)
    (hperm : (ct.lits.map (vl M)).Perm
      (([⟨1,0,1,0,21⟩,⟨3,1,2,0,21⟩,⟨7,2,0,0,21⟩,
         ⟨6,0,3,0,21⟩,⟨14,3,2,0,21⟩,⟨10,2,4,0,21⟩] : List Centre).flatMap corners))
    (hk : ct.k = 22) :
    JointTags.Good (sel p (amap P (vx p r))) E M ct := by
  constructor
  · apply List.all_eq_true.2
    intro x hx
    have hn := List.all_eq_true.1 hneg x hx
    simp only [negP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
    simp [baseOK, hn.1.2, hn.2]
  · obtain ⟨h1,h2,h3,h4,h5,h6⟩ := frame_counts p P r hr hP
    have hc := SumCountSemantics112.countP_permuted_corners
      (sel p (amap P (vx p r))) E M ct.lits _ hneg hperm
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hc
    rw [h1,h2,h3,h4,h5,h6] at hc
    rw [hc,hk]
    simpa [Finset.sum_range_succ,Nat.add_assoc] using htotal

theorem actual_three_counter_good {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0)
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22)
    (hfourth : coreAlpha p (r+4) = 3)
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
  · obtain ⟨h1,h2,h3,h4,h5,h6⟩ := frame_counts p P r hr hP
    have hc := SumCountSemantics112.countP_permuted_corners
      (sel p (amap P (vx p r))) E M ct.lits _ hneg hperm
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hc
    rw [h3,h5,h6] at hc
    rw [hc,hk]
    simpa only [Nat.add_assoc] using
      (ActualSplit129.actual_equality_consequences p r hr hshape htotal hfourth).2.2

#print axioms actual_window_axioms
#print axioms actual_total_counter_good
#print axioms actual_three_counter_good
end Snake9.ActualCounters129
