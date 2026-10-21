import SquareIncidence

/-!
# Corner share: the global charge inequality (stage 0)

Implements §1 of `milestones/11-local-ceiling/s0_lean_design.md`.  On top of
`SquareIncidence` (global identity, wedge bound, selected count) this file defines the
integer corner share `shareN M p x` of resolution `M` and proves

* `share_double_count` : `Σ_x sel(x)·shareN(x) = Σ_q d(q)·⌊M e0(q)/d(q)⌋`,
* `share_total_le`     : `Σ_x sel(x)·shareN(x) ≤ M · totalEmptyAnchored p`,
* `charge_total_le`    : `Σ_x sel(x)·(2M α(x) + shareN(x)) + 70 M (m+1) ≤ 18428 M` (for `1 ≤ m`).

The last one is `M ×` the strengthened incidence bound
`totalEmptyAnchored + 2·totalSingleton + 70 (m+1) ≤ 18428` (`incidence_bound_with_empty`),
which is `global_identity` + `wedge_total_upper` + `selected_total` without dropping the
empty-square term, plus `share_total_le`.
-/

namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset
open Classical
noncomputable section
set_option maxHeartbeats 2000000

/-- Empty squares containing `q` (`empty` is anchored at every corner, so this is
`e0(q)`); zero when `q` is selected. -/
def emptyAt {m : Nat} (p : Snake m) (q : Vertex) : Nat := ∑ ab : AxisPair, empty p ab q

/-- Selected neighbours `d(q)`. -/
def selDeg {m : Nat} (p : Snake m) (q : Vertex) : Nat := ∑ k : Coord, selected p (flip k q)

/-- Integer corner share of resolution `M` received by `x` from its nine neighbours. -/
def shareN {m : Nat} (M : Nat) (p : Snake m) (x : Vertex) : Nat :=
  ∑ k : Coord, M * emptyAt p (flip k x) / selDeg p (flip k x)

theorem emptyAt_total {m : Nat} (p : Snake m) : (∑ q, emptyAt p q) = totalEmptyAnchored p := by
  unfold emptyAt totalEmptyAnchored
  exact Finset.sum_comm

/-- `emptyAt` vanishes at selected vertices. -/
theorem emptyAt_eq_zero_of_inPath {m : Nat} (p : Snake m) (q : Vertex) (hq : InPath p q) :
    emptyAt p q = 0 := by
  unfold emptyAt
  apply Finset.sum_eq_zero
  intro ab _
  unfold empty
  rw [if_neg]
  intro h
  exact h.1 hq

/-- Reindexing one coordinate: `Σ_x sel(x) f(flip k x) = Σ_q sel(flip k q) f(q)`. -/
theorem sum_selected_flip {m : Nat} (p : Snake m) (k : Coord) (f : Vertex → Nat) :
    (∑ x, selected p x * f (flip k x)) = ∑ q, selected p (flip k q) * f q := by
  have h := sum_flip k (fun q => selected p (flip k q) * f q)
  simp only [flip_twice] at h
  exact h

theorem share_double_count {m : Nat} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * shareN M p x) =
      ∑ q, selDeg p q * (M * emptyAt p q / selDeg p q) := by
  unfold shareN selDeg
  calc
    (∑ x, selected p x * ∑ k : Coord, M * emptyAt p (flip k x) / selDeg p (flip k x))
        = ∑ x, ∑ k : Coord, selected p x * (M * emptyAt p (flip k x) / selDeg p (flip k x)) := by
          apply Finset.sum_congr rfl
          intro x _
          exact Finset.mul_sum _ _ _
    _ = ∑ k : Coord, ∑ x, selected p x * (M * emptyAt p (flip k x) / selDeg p (flip k x)) :=
          Finset.sum_comm
    _ = ∑ k : Coord, ∑ q, selected p (flip k q) * (M * emptyAt p q / selDeg p q) := by
          apply Finset.sum_congr rfl
          intro k _
          exact sum_selected_flip p k (fun q => M * emptyAt p q / selDeg p q)
    _ = ∑ q, ∑ k : Coord, selected p (flip k q) * (M * emptyAt p q / selDeg p q) :=
          Finset.sum_comm
    _ = ∑ q, (∑ k : Coord, selected p (flip k q)) * (M * emptyAt p q / selDeg p q) := by
          apply Finset.sum_congr rfl
          intro q _
          exact (Finset.sum_mul _ _ _).symm

theorem share_total_le {m : Nat} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * shareN M p x) ≤ M * totalEmptyAnchored p := by
  rw [share_double_count, ← emptyAt_total, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  exact Nat.mul_div_le (M * emptyAt p q) (selDeg p q)

/-- The incidence bound keeping the empty-square term:
`TEA + 2 T + 70 (m+1) ≤ 18428` (the existing aggregates use `T + 35 (m+1) ≤ 9214`,
i.e. this with `TEA ≥ 0` dropped and halved).  Needs `1 ≤ m`: for the one-vertex snake
`totalWedge = 0 = m - 1` gives no slack and the bound fails by `2`
(`TEA = 18288`, `T = 36`, so the left side is `18430`). -/
theorem incidence_bound_with_empty {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    totalEmptyAnchored p + 2 * totalSingleton p + 70 * (m + 1) ≤ 18428 := by
  have hid := global_identity p
  rw [selected_total p] at hid
  have hw := wedge_total_upper p
  omega

/-- `Σ_x sel(x)·α(x) = totalSingleton p` (`singleton` vanishes at unselected `x`). -/
theorem selected_singleton_total {m : Nat} (p : Snake m) :
    (∑ x, selected p x * ∑ ab : AxisPair, singleton p ab x) = totalSingleton p := by
  have hx (x : Vertex) : selected p x * (∑ ab : AxisPair, singleton p ab x)
      = ∑ ab : AxisPair, singleton p ab x := by
    by_cases hv : InPath p x
    · rw [selected, if_pos hv, one_mul]
    · rw [selected, if_neg hv, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro ab _
      unfold singleton
      rw [if_neg]
      intro h
      exact hv h.1
  simp only [hx]
  unfold totalSingleton
  exact Finset.sum_comm

/-- The weighted incidence inequality:
`Σ_x sel(x)·(2M α(x) + shareN_M(x)) + 70 M (m+1) ≤ 18428 M`. -/
theorem charge_total_le {m : Nat} (M : Nat) (p : Snake m) (hm : 1 ≤ m) :
    (∑ x, selected p x * (2 * M * (∑ ab : AxisPair, singleton p ab x) + shareN M p x))
      + 70 * M * (m + 1) ≤ 18428 * M := by
  have hsplit : (∑ x, selected p x * (2 * M * (∑ ab : AxisPair, singleton p ab x) + shareN M p x))
      = 2 * M * (∑ x, selected p x * ∑ ab : AxisPair, singleton p ab x)
        + ∑ x, selected p x * shareN M p x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsplit, selected_singleton_total]
  have hsh := share_total_le M p
  have hinc := Nat.mul_le_mul_left M (incidence_bound_with_empty p hm)
  nlinarith [hsh, hinc]

#print axioms share_double_count
#print axioms share_total_le
#print axioms incidence_bound_with_empty
#print axioms charge_total_le
end
end Snake9.SquareIncidence
