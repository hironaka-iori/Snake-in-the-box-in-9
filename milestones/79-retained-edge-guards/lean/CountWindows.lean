import CanonicalExclusions

namespace Snake9.Guards79
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation74 Snake9.GraphInterpretation75
open Snake9.GraphWalk78 Snake9.CountGeometry78
set_option maxHeartbeats 2000000

theorem symC_eq_min (a : Nat) : symC a = min 6 a := by
  unfold symC
  split_ifs <;> omega

theorem symsOf_slice {m : Nat} (p : Snake m) (r n s w : Nat)
    (hs : s+w ≤ n-1) :
    ((symsOf p r n).drop s).take w = symsOf p (r+s) (w+1) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, length_symsOf]
    omega
  · intro i hi hj
    have hiw : i < w := by simpa only [length_symsOf, Nat.add_sub_cancel] using hj
    simp only [symsOf, List.getElem_take, List.getElem_drop, List.getElem_map,
      List.getElem_range, Nat.add_sub_cancel]
    congr 2 <;> omega

theorem canonical_nine_slice {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hs : s+w ≤ 9) :
    canon (((canon (dsOf p r 9)).drop s).take w) =
      canon (dsOf p (r+s) w) := by
  rw [← canon_canon_take, canon_canon_drop, canon_canon_take,
    dsOf_slice p r 9 s w hr hs]

def sixSymbols {m : Nat} (p : Snake m) (r : Nat) : List Nat :=
  symsOf p (r+2) 7

theorem sixSymbols_explicit {m : Nat} (p : Snake m) (r : Nat) :
    sixSymbols p r = [truncatedCount p (r+3), truncatedCount p (r+4),
      truncatedCount p (r+5), truncatedCount p (r+6),
      truncatedCount p (r+7), truncatedCount p (r+8)] := by
  simp [sixSymbols, symsOf, List.range_succ, symC_eq_min, truncatedCount, Nat.add_assoc]

theorem sixSymbols_code {m : Nat} (p : Snake m) (r : Nat) :
    encodeCounts (sixSymbols p r) 0 = sixCode p r := by
  rw [sixSymbols_explicit]; rfl

theorem actual_symbol_slice {m : Nat} (p : Snake m) (r s w : Nat)
    (hs : s+w ≤ 6) :
    ((sixSymbols p r).drop s).take w = symsOf p (r+s+2) (w+1) := by
  have h := symsOf_slice p (r+2) 7 s w (by omega)
  simpa only [sixSymbols, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem six_code_slice (a b c d e f s w : Nat)
    (ha : 1 ≤ a ∧ a ≤ 6) (hb : 1 ≤ b ∧ b ≤ 6)
    (hc : 1 ≤ c ∧ c ≤ 6) (hd : 1 ≤ d ∧ d ≤ 6)
    (he : 1 ≤ e ∧ e ≤ 6) (hf : 1 ≤ f ∧ f ≤ 6)
    (hw : 2 ≤ w) (hs : s+w ≤ 6) :
    encodeCounts [a,b,c,d,e,f] 0 / 6^(6-s-w) % 6^w =
      encodeCounts (([a,b,c,d,e,f].drop s).take w) 0 := by
  have hw6 : w ≤ 6 := by omega
  have hs6 : s ≤ 6 := by omega
  interval_cases w <;> interval_cases s <;>
    simp only [encodeCounts, List.drop, List.take, Nat.reducePow,
      Nat.reduceSub, Nat.zero_mul, Nat.zero_add] <;> omega

theorem actual_code_slice {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hw : 2 ≤ w) (hs : s+w ≤ 6) :
    sixCode p r / 6^(6-s-w) % 6^w =
      encodeCounts (symsOf p (r+s+2) (w+1)) 0 := by
  rw [← actual_symbol_slice p r s w hs, sixSymbols_explicit]
  exact six_code_slice _ _ _ _ _ _ s w
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega))
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega))
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega)) hw hs

#print axioms symC_eq_min
#print axioms symsOf_slice
#print axioms canonical_nine_slice
#print axioms sixSymbols_explicit
#print axioms sixSymbols_code
#print axioms actual_symbol_slice
#print axioms six_code_slice
#print axioms actual_code_slice
end Snake9.Guards79
