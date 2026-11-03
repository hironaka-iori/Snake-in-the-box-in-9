import CanonicalExclusions
import JointCountBridge
import JointCountTags

namespace Snake9.LargeLower130
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.LocalWindow.Tags

set_option maxHeartbeats 2000000

local notation "fourthCorners" =>
  ([0,20,36,68,132,260,18,34,66,130,258,54,86,150,278,102,166,294,198,326,390] : List Nat)

theorem corner_list_eq : fourthCorners = corners ⟨6,0,3,0,21⟩ := by
  decide +kernel

theorem selected_absent_identity (S : Nat → Bool) :
    (fourthCorners).countP S + absentCorners S 6 0 3 = 21 := by
  have h := countP_corners_sel (S := S) (⟨6,0,3,0,21⟩ : Centre)
  have hl : (freePairs 0 3).length = 21 := by decide +kernel
  change (corners ⟨6,0,3,0,21⟩).countP S + absentCorners S 6 0 3 =
    (freePairs 0 3).length at h
  rw [corner_list_eq]
  exact hl ▸ h

theorem actual_selected_bound {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0)
    (hfourth : 4 ≤ coreAlpha p (r+4)) :
    (fourthCorners).countP (sel p (amap P (vx p r))) ≤ 17 := by
  have hc : Canon (winOf [0,1,2,0,3,2,4]) [0,1,2,0,3,2,4] := canon_winOf _
  have h4 := JointTags.frame_count p P r hc hr hP 3 (by decide)
  have hw : winOf [0,1,2,0,3,2,4] = [0,1,3,7,6,14,10,26] := by decide +kernel
  have hd : dirOfStep 7 6 = 0 ∧ dirOfStep 6 14 = 3 := by
    simp only [Tags.dirOfStep_eq]
    decide +kernel
  norm_num [hw,hd.1,hd.2,Nat.add_assoc] at h4
  have h := selected_absent_identity (sel p (amap P (vx p r)))
  rw [h4] at h
  omega

theorem actual_normalized_bound {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hfourth : 4 ≤ coreAlpha p (r+4)) :
    ∃ P : CPerm,
      (∀ j, j < 7 → P.fwd (dir p (r+j)) =
        ([0,1,2,0,3,2,4] : List Nat).getD j 0) ∧
      (fourthCorners).countP (sel p (amap P (vx p r))) ≤ 17 := by
  obtain ⟨u,hu,hu9,huLen,hcs⟩ := actual_canonical_frame p r 7 hr
  have hsp := mkPerm_spec hu hu9 huLen
  have hP : ∀ j, j < 7 → (mkPerm u).fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0 := by
    intro j hj
    obtain ⟨hi,hd⟩ := hcs j hj
    rw [hshape] at hi hd
    rw [← hd]
    exact hsp _ hi
  exact ⟨mkPerm u,hP,actual_selected_bound p (mkPerm u) r hr hP hfourth⟩

theorem actual_counter_good {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0)
    (hfourth : 4 ≤ coreAlpha p (r+4))
    (E : Nat → Bool) (M : MT) (ct : Ctr)
    (hpos : ct.lits.all (posP M) = true)
    (hmap : ct.lits.map (vl M) = fourthCorners) (hk : ct.k = 17) :
    JointTags.Good (sel p (amap P (vx p r))) E M ct := by
  constructor
  · apply List.all_eq_true.2
    intro x hx
    have hp := List.all_eq_true.1 hpos x hx
    simp only [posP,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hp
    simp [baseOK,hp.1.2,hp.2]
  · have hcount : ct.lits.countP
        (lv (base (sel p (amap P (vx p r))) E M)) =
        (ct.lits.map (vl M)).countP (sel p (amap P (vx p r))) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro x hx
      simp [base_posP (List.all_eq_true.1 hpos x hx)]
    rw [hcount,hmap,hk]
    exact actual_selected_bound p P r hr hP hfourth

#print axioms corner_list_eq
#print axioms selected_absent_identity
#print axioms actual_selected_bound
#print axioms actual_normalized_bound
#print axioms actual_counter_good
end Snake9.LargeLower130
