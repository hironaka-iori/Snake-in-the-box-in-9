import CountWindows
import BaseSix

namespace Snake9.Guards79
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
set_option maxHeartbeats 2000000

theorem symsOf_valid {m : Nat} (p : Snake m) (r n : Nat) (hr : r+n ≤ m) :
    ∀ x ∈ symsOf p r n, 1 ≤ x ∧ x ≤ 6 := by
  intro x hx
  simp only [symsOf, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [symC_eq_min]
  exact truncatedCount_range p _ (by omega)

theorem actual_slice_decode {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hw : 2 ≤ w) (hs : s+w ≤ 6)
    (syms : List Nat) (hlen : syms.length = w)
    (hvalid : ∀ x ∈ syms, 1 ≤ x ∧ x ≤ 6)
    (hcode : sixCode p r / 6^(6-s-w) % 6^w = encodeCounts syms 0) :
    symsOf p (r+s+2) (w+1) = syms := by
  apply encode_injective _ _ (symsOf_valid p _ _ (by omega)) hvalid
  · simp only [length_symsOf, Nat.add_sub_cancel]; exact hlen.symm
  · rw [← actual_code_slice p r s w hr hw hs]; exact hcode

theorem reverse_canon (ds : List Nat) : canon (canon ds).reverse = canon ds.reverse := by
  simpa only [List.drop_zero] using canon_canon_drop_reverse ds 0

theorem canonical_nine_slice_reverse {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hs : s+w ≤ 9) :
    canon (((canon (dsOf p r 9)).drop s).take w).reverse =
      canon (dsOf p (r+s) w).reverse := by
  rw [← reverse_canon (((canon (dsOf p r 9)).drop s).take w),
    canonical_nine_slice p r s w hr hs, reverse_canon]

theorem encoded_forward_exclusion {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hw : 2 ≤ w) (hs : s+w ≤ 6)
    (cs syms : List Nat) (hlen : syms.length = w)
    (hvalid : ∀ x ∈ syms, 1 ≤ x ∧ x ≤ 6)
    (href : Refuted (winOf cs) (boundsOf syms))
    (hshape : canon (((canon (dsOf p r 9)).drop (s+2)).take (w+1)) = cs)
    (hcode : sixCode p r / 6^(6-s-w) % 6^w = encodeCounts syms 0) : False := by
  have hshape' : canon (dsOf p (r+s+2) (w+1)) = cs := by
    simpa only [Nat.add_assoc] using
      ((canonical_nine_slice p r (s+2) (w+1) hr (by omega)).symm.trans hshape)
  exact canonical_symbol_exclusion p (r+s+2) (w+1) cs syms (by omega) (by omega)
    hshape' (actual_slice_decode p r s w hr hw hs syms hlen hvalid hcode) href

theorem encoded_reverse_exclusion {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+9 ≤ m) (hw : 2 ≤ w) (hs : s+w ≤ 6)
    (cs syms : List Nat) (hlen : syms.length = w)
    (hvalid : ∀ x ∈ syms, 1 ≤ x ∧ x ≤ 6)
    (href : Refuted (winOf cs) (boundsOf syms))
    (hshape : canon ((((canon (dsOf p r 9)).drop (s+2)).take (w+1)).reverse) = cs)
    (hcode : sixCode p r / 6^(6-s-w) % 6^w = encodeCounts syms.reverse 0) : False := by
  have hshape' : canon (dsOf p (r+s+2) (w+1)).reverse = cs := by
    simpa only [Nat.add_assoc] using
      ((canonical_nine_slice_reverse p r (s+2) (w+1) hr (by omega)).symm.trans hshape)
  have hdecode := actual_slice_decode p r s w hr hw hs syms.reverse
    (by simpa using hlen) (fun x hx => hvalid x (List.mem_reverse.mp hx)) hcode
  apply reversed_symbol_exclusion p (r+s+2) (w+1) cs syms (by omega) (by omega)
    hshape' _ href
  rw [hdecode, List.reverse_reverse]

#print axioms symsOf_valid
#print axioms actual_slice_decode
#print axioms reverse_canon
#print axioms canonical_nine_slice_reverse
#print axioms encoded_forward_exclusion
#print axioms encoded_reverse_exclusion
end Snake9.Guards79
