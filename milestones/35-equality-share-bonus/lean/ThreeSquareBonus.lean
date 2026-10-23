import LocalWindowSat.PairShareCert
import LocalWindowUnsat.PairShareCert
import LocalWindowShareBridge
import DistanceThreeFresh
namespace Snake9.LocalWindow.PairShareCert
set_option maxHeartbeats 0

theorem local_share_lower (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds)) :
    12 ≤ shareSum 12 S shareCentres := by
  by_contra! h
  obtain ⟨τ,hτ⟩ := sat S E ax (by omega)
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def directions : List Nat := [0,1,2,3,4,1,5]

theorem share_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) = directions.getD j 0) :
    12 ≤ coreShare 12 p (r+1) + coreShare 12 p (r+6) := by
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
  have h := local_share_lower _ _ ax
  have f1 := frame_window p P r hc hr hP 1 (by decide)
  have f6 := frame_window p P r hc hr hP 6 (by decide)
  have s1 := shareLocal_frame p P (vx p r) (vx_lt p r) (vx_lt p (r+1)) 12
  have s6 := shareLocal_frame p P (vx p r) (vx_lt p r) (vx_lt p (r+6)) 12
  change window.getD 1 0 = _ at f1
  change window.getD 6 0 = _ at f6
  change centreA.v = _ at f1
  change centreB.v = _ at f6
  change 12 ≤ shareLocal 12 _ centreA.v + (shareLocal 12 _ centreB.v + 0) at h
  rw [f1,f6,s1,s6,Nat.add_zero] at h
  exact h

theorem pattern_share_in_snake {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x < 9)
    (hr : r+7 ≤ m)
    (hd : ∀ j, j < 7 → dir p (r+j) = ([a,b,c,d,e,b,f] : List Nat).getD j 0) :
    12 ≤ coreShare 12 p (r+1) + coreShare 12 p (r+6) := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply share_in_snake p (mkPerm [a,b,c,d,e,f]) r hr
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

theorem pattern_charge_in_snake {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x < 9)
    (hr : r+7 ≤ m)
    (hd : ∀ j, j < 7 → dir p (r+j) = ([a,b,c,d,e,b,f] : List Nat).getD j 0) :
    228 ≤ 24*(coreAlpha p (r+1)+coreAlpha p (r+6)) +
      coreShare 12 p (r+1)+coreShare 12 p (r+6) := by
  have ha := DistanceThree1.pattern_sum_in_snake p r a b c d e f hn h9 hr hd
  have hs := pattern_share_in_snake p r a b c d e f hn h9 hr hd
  omega

#print axioms local_share_lower
#print axioms share_in_snake
#print axioms pattern_share_in_snake
#print axioms pattern_charge_in_snake
end Snake9.LocalWindow.PairShareCert
