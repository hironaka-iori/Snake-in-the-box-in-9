import ShareCharge
import Mathlib.Tactic

namespace Snake9.EmptySquarePacking
open Finset SquareIncidence
open scoped BigOperators
noncomputable section

/-- Exact loss of the integer corner charge, including undominated corners:
Nat.mod n 0 = n, so their entire contribution is recorded as loss. -/
theorem share_loss_identity {m : Nat} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * shareN M p x) +
      (∑ q, (M * emptyAt p q) % selDeg p q) = M * totalEmptyAnchored p := by
  rw [share_double_count, ← Finset.sum_add_distrib, ← emptyAt_total, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have h := Nat.mod_add_div (M * emptyAt p q) (selDeg p q)
  omega

/-- Any collection of local lower bounds can be combined with nonnegative
integer weights, provided the total weight at each vertex is at most C. -/
theorem weighted_window_packing {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V]
    (W : I → Finset V) (lower weight : I → Nat) (share : V → Nat) (C : Nat)
    (hlocal : ∀ i, lower i ≤ ∑ v ∈ W i, share v)
    (hcapacity : ∀ v, (∑ i, if v ∈ W i then weight i else 0) ≤ C) :
    (∑ i, weight i * lower i) ≤ C * ∑ v, share v := by
  classical
  have he (i : I) : weight i * (∑ v ∈ W i, share v) =
      ∑ v, (if v ∈ W i then weight i else 0) * share v := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.mul_sum _ _ _
  calc
    (∑ i, weight i * lower i) ≤ ∑ i, weight i * ∑ v ∈ W i, share v :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hlocal i))
    _ = ∑ v, (∑ i, if v ∈ W i then weight i else 0) * share v := by
      simp only [he]
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ v, C * share v := Finset.sum_le_sum
      (fun v _ => Nat.mul_le_mul_right _ (hcapacity v))
    _ = C * ∑ v, share v := (Finset.mul_sum _ _ _).symm

/-- A five-position packing recurrence. The lower bound b i concerns exactly
positions i,...,i+4. Missing certificates may safely use b i = 0. -/
theorem five_window_dp_sound (s b D : Nat → Nat)
    (h0 : D 0 = 0)
    (hstep : ∀ n, D (n+1) = max (D n)
      (if 5 ≤ n+1 then D (n+1-5) + b (n+1-5) else 0))
    (hlower : ∀ i, b i ≤ ∑ j ∈ Finset.range 5, s (i+j)) :
    ∀ n, D n ≤ ∑ j ∈ Finset.range n, s j := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [h0]
    | succ k =>
      rw [hstep]
      apply max_le
      · have hk := ih k (by omega)
        rw [Finset.sum_range_succ]
        omega
      · split_ifs with h
        · have hp := ih (k+1-5) (by omega)
          have hb := hlower (k+1-5)
          have hn : k+1 = (k+1-5)+5 := by omega
          rw [hn, Finset.sum_range_add]
          simp only [Nat.add_sub_cancel]
          omega
        · exact Nat.zero_le _

#print axioms share_loss_identity
#print axioms weighted_window_packing
#print axioms five_window_dp_sound

/-- Concrete packing of two disjoint windows in the saved eleven-position
pattern. The two numerical local bounds remain explicit hypotheses. -/
theorem eleven_cycle_packing (s : Fin 11 → Nat)
    (h0 : 163 ≤ s 0 + s 1 + s 2 + s 3 + s 4)
    (h6 : 301 ≤ s 6 + s 7 + s 8 + s 9 + s 10) :
    464 ≤ ∑ i, s i := by
  simp only [Fin.sum_univ_succ]
  norm_num
  change 464 ≤ s 0 + (s 1 + (s 2 + (s 3 + (s 4 + (s 5 + (s 6 + (s 7 + (s 8 + (s 9 + s 10)))))))))
  omega

/-- Exact numerical target for 230 edges, retaining a finite boundary loss
of 191 integer share units at resolution M = 12. -/
theorem upper230_of_charge {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (hlower : 114 * (m+1) ≤
      (∑ x, selected p x * (24 * (∑ ab : AxisPair, singleton p ab x) + shareN 12 p x)) + 191) :
    m ≤ 230 := by
  have h := charge_total_le 12 p hm
  norm_num at h
  omega

theorem upper231_of_charge {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (hlower : 114 * (m+1) ≤
      (∑ x, selected p x * (24 * (∑ ab : AxisPair, singleton p ab x) + shareN 12 p x)) + 1145) :
    m ≤ 231 := by
  have h := charge_total_le 12 p hm
  norm_num at h
  omega

#print axioms eleven_cycle_packing
#print axioms upper230_of_charge
#print axioms upper231_of_charge
end
end Snake9.EmptySquarePacking
