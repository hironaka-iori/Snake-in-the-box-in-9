import NumericRetention

namespace Snake9.Boxes88
open Snake9.Guards79 Snake9.GraphInterpretation75
set_option maxHeartbeats 2000000

theorem digit_range (code j : Nat) : 1 ≤ digit code j ∧ digit code j ≤ 6 := by
  unfold digit
  omega

def digits (code : Nat) : List Nat := (List.range 6).map (digit code)

theorem digits_explicit (code : Nat) :
    digits code = [digit code 0,digit code 1,digit code 2,
      digit code 3,digit code 4,digit code 5] := by rfl

theorem digit_reconstruction (code : Nat) (hc : code < 46656) :
    encodeCounts (digits code) 0 = code := by
  rw [digits_explicit]
  simp only [digit, encodeCounts, Nat.reducePow, Nat.reduceSub,
    Nat.zero_mul, Nat.zero_add]
  omega

theorem digit_slice (code s w : Nat) (hc : code < 46656)
    (hw : 2 ≤ w) (hs : s+w ≤ 6) :
    code / 6^(6-s-w) % 6^w = encodeCounts (((digits code).drop s).take w) 0 := by
  have h := six_code_slice (digit code 0) (digit code 1) (digit code 2)
    (digit code 3) (digit code 4) (digit code 5) s w
    (digit_range _ _) (digit_range _ _) (digit_range _ _)
    (digit_range _ _) (digit_range _ _) (digit_range _ _) hw hs
  rw [← digits_explicit, digit_reconstruction code hc] at h
  exact h

theorem digit_slice_eq (code s : Nat) (xs : List Nat) (hs : s+xs.length ≤ 6)
    (h : ∀ i, i < xs.length → digit code (s+i) = xs.getD i 0) :
    ((digits code).drop s).take xs.length = xs := by
  apply List.ext_getElem
  · simp [digits]; omega
  · intro i hi hj
    simp only [digits, List.getElem_take, List.getElem_drop, List.getElem_map,
      List.getElem_range]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some] using h i hj

theorem digit_slice_code (code s : Nat) (xs : List Nat) (hc : code < 46656)
    (hw : 2 ≤ xs.length) (hs : s+xs.length ≤ 6)
    (h : ∀ i, i < xs.length → digit code (s+i) = xs.getD i 0) :
    code / 6^(6-s-xs.length) % 6^xs.length = encodeCounts xs 0 := by
  rw [digit_slice code s xs.length hc hw hs, digit_slice_eq code s xs hs h]

#print axioms digit_range
#print axioms digit_reconstruction
#print axioms digit_slice
#print axioms digit_slice_eq
#print axioms digit_slice_code
end Snake9.Boxes88
