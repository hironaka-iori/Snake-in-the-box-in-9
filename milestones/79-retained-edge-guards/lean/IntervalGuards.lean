import ReferenceRetention

namespace Snake9.Guards79
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
set_option maxHeartbeats 2000000

def digit (code j : Nat) : Nat := code / 6^(5-j) % 6 + 1

theorem six_code_digit (a b c d e f j : Nat)
    (ha : 1 ≤ a ∧ a ≤ 6) (hb : 1 ≤ b ∧ b ≤ 6)
    (hc : 1 ≤ c ∧ c ≤ 6) (hd : 1 ≤ d ∧ d ≤ 6)
    (he : 1 ≤ e ∧ e ≤ 6) (hf : 1 ≤ f ∧ f ≤ 6) (hj : j < 6) :
    digit (encodeCounts [a,b,c,d,e,f] 0) j = [a,b,c,d,e,f].getD j 0 := by
  interval_cases j <;> simp only [digit, encodeCounts, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reducePow, Nat.reduceSub, Nat.zero_mul, Nat.zero_add] <;> omega

theorem actual_digit {m : Nat} (p : Snake m) (r j : Nat)
    (hr : r+9 ≤ m) (hj : j < 6) :
    digit (sixCode p r) j = truncatedCount p (r+j+3) := by
  have h := six_code_digit _ _ _ _ _ _ j
    (truncatedCount_range p (r+3) (by omega)) (truncatedCount_range p (r+4) (by omega))
    (truncatedCount_range p (r+5) (by omega)) (truncatedCount_range p (r+6) (by omega))
    (truncatedCount_range p (r+7) (by omega)) (truncatedCount_range p (r+8) (by omega)) hj
  rw [← sixSymbols_explicit] at h
  have heq : (sixSymbols p r).getD j 0 = truncatedCount p (r+j+3) := by
    unfold sixSymbols
    rw [getD_symsOf p (by omega : j < 7-1), symC_eq_min]
    simp only [truncatedCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa only [sixSymbols_code] using h.trans heq

theorem truncated_interval (a lo hi : Nat) (ha : a ≤ 21)
    (hlo : lo ≤ 6) (hhi : hi < 6 ∨ hi = 21) :
    (lo ≤ min 6 a ∧ min 6 a ≤ hi) ↔ (lo ≤ a ∧ a ≤ hi) := by
  rcases hhi with hhi | hhi <;> omega

def intervalHit (code s w : Nat) (reverse : Bool) (bounds : List (Nat × Nat)) : Prop :=
  ∀ i, i < bounds.length →
    (bounds.getD i (0,21)).1 ≤ digit code (s + if reverse then w-1-i else i) ∧
    digit code (s + if reverse then w-1-i else i) ≤ (bounds.getD i (0,21)).2

theorem encoded_interval_forward_exclusion {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hw : 1 ≤ w) (hs : s+w ≤ 6)
    (cs : List Nat) (bounds : List (Nat × Nat)) (hlen : bounds.length = w)
    (hends : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ 6 ∧
      ((bounds.getD i (0,21)).2 < 6 ∨ (bounds.getD i (0,21)).2 = 21))
    (href : Refuted (winOf cs) bounds)
    (hshape : canon (((canon (dsOf p r 9)).drop (s+2)).take (w+1)) = cs)
    (hhit : intervalHit (sixCode p r) s w false bounds) : False := by
  apply canonical_interval_exclusion p (r+s+2) (w+1) cs bounds (by omega) (by omega)
  · simpa only [Nat.add_assoc] using
      ((canonical_nine_slice p r (s+2) (w+1) hr (by omega)).symm.trans hshape)
  · exact href
  · intro i hi
    have hg := hhit i hi
    simp only [Bool.false_eq_true, ↓reduceIte] at hg
    rw [actual_digit p r (s+i) hr (by omega)] at hg
    have h := (truncated_interval (coreAlpha p (r+(s+i)+3))
      (bounds.getD i (0,21)).1 (bounds.getD i (0,21)).2
      (coreAlpha_le_21 p (by omega) (by omega)) (hends i hi).1 (hends i hi).2).mp hg
    have heq : r+(s+i)+3 = r+s+2+i+1 := by omega
    rw [heq] at h
    exact h

theorem encoded_interval_reverse_exclusion {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hw : 1 ≤ w) (hs : s+w ≤ 6)
    (cs : List Nat) (bounds : List (Nat × Nat)) (hlen : bounds.length = w)
    (hends : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ 6 ∧
      ((bounds.getD i (0,21)).2 < 6 ∨ (bounds.getD i (0,21)).2 = 21))
    (href : Refuted (winOf cs) bounds)
    (hshape : canon ((((canon (dsOf p r 9)).drop (s+2)).take (w+1)).reverse) = cs)
    (hhit : intervalHit (sixCode p r) s w true bounds) : False := by
  apply canonical_interval_exclusion (revSnake p) (m-(r+s+2)-(w+1)) (w+1) cs bounds
    (by omega) (by omega)
  · rw [dsOf_rev p (r+s+2) (w+1) (by omega)]
    simpa only [Nat.add_assoc] using
      ((canonical_nine_slice_reverse p r (s+2) (w+1) hr (by omega)).symm.trans hshape)
  · exact href
  · intro i hi
    have hg := hhit i hi
    simp only [↓reduceIte] at hg
    rw [actual_digit p r (s+(w-1-i)) hr (by omega)] at hg
    have h := (truncated_interval (coreAlpha p (r+(s+(w-1-i))+3))
      (bounds.getD i (0,21)).1 (bounds.getD i (0,21)).2
      (coreAlpha_le_21 p (by omega) (by omega)) (hends i hi).1 (hends i hi).2).mp hg
    rw [coreAlpha_rev p (by omega)]
    have heq : m-(m-(r+s+2)-(w+1)+i+1) = r+(s+(w-1-i))+3 := by omega
    rw [heq]
    exact h

#print axioms six_code_digit
#print axioms actual_digit
#print axioms truncated_interval
#print axioms encoded_interval_forward_exclusion
#print axioms encoded_interval_reverse_exclusion
end Snake9.Guards79
