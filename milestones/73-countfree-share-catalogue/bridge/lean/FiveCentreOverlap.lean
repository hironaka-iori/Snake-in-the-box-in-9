import CoreShareBudget

/-!
Five-centre overlap accounting. The sum-commutation argument is the unweighted
interval specialization of milestone 27's `weighted_window_packing`; its reference
source and hash are recorded in data/overlap-reference.json. The interval capacity
is established here by comparing each of the five shifted sums with the whole path.
-/
namespace Snake9.CountFreeBridge
open Finset SquareIncidence LocalWindow
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

theorem shifted_prefix_sum_le (f : Nat → Nat) (a n N : Nat) (h : a+n ≤ N) :
    (∑ r ∈ Finset.range n, f (r+a)) ≤ ∑ k ∈ Finset.range N, f k := by
  calc
    _ ≤ (∑ k ∈ Finset.range a, f k) + ∑ r ∈ Finset.range n, f (r+a) :=
      Nat.le_add_left _ _
    _ = ∑ k ∈ Finset.range (a+n), f k := by
      rw [Finset.sum_range_add]
      simp only [Nat.add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
      (by intro i _ _; exact Nat.zero_le _)

/-- Every position is counted at most five times among all five-centre windows.
The natural-number truncation makes the statement valid also for m < 6. -/
theorem five_centre_overlap (f : Nat → Nat) (m : Nat) :
    (∑ r ∈ Finset.range (m-5), ∑ i ∈ Finset.range 5, f (r+i+1)) ≤
      5 * ∑ k ∈ Finset.range (m+1), f k := by
  by_cases hm : 5 ≤ m
  · rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (m+1), f k := by
        apply Finset.sum_le_sum
        intro i hi
        have hi5 : i < 5 := Finset.mem_range.mp hi
        simpa only [Nat.add_assoc] using
          shifted_prefix_sum_le f (i+1) (m-5) (m+1) (by omega)
      _ = _ := by simp [Nat.mul_comm]
  · have hz : m-5=0 := by omega
    simp [hz]

theorem five_centre_overlap_list (f : Nat → Nat) (m : Nat) :
    ((List.range (m-5)).map fun r =>
      ((List.range 5).map fun i => f (r+i+1)).sum).sum ≤
        5 * ((List.range (m+1)).map f).sum := by
  simpa only [sum_range_eq_list_sum] using five_centre_overlap f m

theorem core_share_five_centre_overlap {m : Nat} (M : Nat) (p : Snake m) :
    ((List.range (m-5)).map fun r =>
      ((List.range 5).map fun i => coreShare M p (r+i+1)).sum).sum ≤
        5 * ((List.range (m+1)).map fun k => coreShare M p k).sum :=
  five_centre_overlap_list (coreShare M p) m

/-- The overlap budget uses the whole path singleton total. A finite graph may
omit boundary counts; accounting for that omission is a separate obligation. -/
theorem core_share12_five_centre_charge_le {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    120*totalSingleton p +
      ((List.range (m-5)).map fun r =>
        ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum).sum +
      4200*(m+1) ≤ 1105680 := by
  have ho := core_share_five_centre_overlap 12 p
  have hb := core_share12_charge_le p hm
  omega

#print axioms shifted_prefix_sum_le
#print axioms five_centre_overlap
#print axioms five_centre_overlap_list
#print axioms core_share_five_centre_overlap
#print axioms core_share12_five_centre_charge_le
end
end Snake9.CountFreeBridge
