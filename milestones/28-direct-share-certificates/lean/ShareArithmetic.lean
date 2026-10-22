import Mathlib.Tactic

namespace Snake9.ShareArithmetic
open Finset
open scoped BigOperators

/-- Exact quotient arithmetic used by the independent model. -/
theorem quotient_iff (N d u : Nat) (hd : 0 < d) :
    N / d = u ↔ u*d ≤ N ∧ N < (u+1)*d := by
  rw [Nat.div_eq_iff hd]
  constructor <;> intro h <;> constructor
  · exact h.1
  · nlinarith [h.2, Nat.sub_add_cancel (show 1 ≤ u*d+d by omega)]
  · exact h.1
  · have hp : 1 ≤ d := hd
    nlinarith [h.2, Nat.sub_add_cancel (show 1 ≤ u*d+d by omega)]

theorem quotient_threshold (N d t : Nat) (hd : 0 < d) :
    t ≤ N/d ↔ t*d ≤ N := Nat.le_div_iff_mul_le hd

/-- Capping each unary contribution at K+1 preserves the test that the total
is at most K. This is the static cap required for refutation certificates. -/
theorem static_cap_iff {I : Type*} [Fintype I] (s : I → Nat) (K : Nat) :
    (∑ i, min (s i) (K+1)) ≤ K ↔ (∑ i, s i) ≤ K := by
  constructor
  · intro h
    have hi (i : I) : s i ≤ K := by
      have hm : min (s i) (K+1) ≤ ∑ j, min (s j) (K+1) :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (min (s j) (K+1))) (Finset.mem_univ i)
      omega
    have he : (∑ i, min (s i) (K+1)) = ∑ i, s i := by
      apply Finset.sum_congr rfl
      intro i _
      exact min_eq_left (by have := hi i; omega)
    rwa [he] at h
  · intro h
    exact le_trans (Finset.sum_le_sum (fun i _ => min_le_left _ _)) h

#print axioms quotient_iff
#print axioms quotient_threshold
#print axioms static_cap_iff
end Snake9.ShareArithmetic
