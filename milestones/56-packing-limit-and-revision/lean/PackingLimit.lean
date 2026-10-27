import Mathlib.Tactic
namespace Snake9.PackingLimit56

def counts : List Nat := [6, 6, 2, 5, 2, 6, 3, 6, 3, 2, 6, 4, 3, 6, 3, 4, 6, 2, 3, 6, 3, 6, 2, 5, 2]
def count (i : Nat) : Int := (counts.getD i 0 : Int)

theorem count_sum : (∑ i ∈ Finset.range 25, count i) = 102 := by decide

theorem potential_sum (c phi : Nat → Int) (A B : Int) (n : Nat)
    (h : ∀ i, i<n → A+phi (i+1) ≤ B*c i+phi i) :
    (n : Int)*A+phi n ≤ B*(∑ i ∈ Finset.range n, c i)+phi 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun i hi => h i (by omega))
    have step := h n (by omega)
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

theorem cycle_mean_ceiling (phi : Nat → Int) (A B : Int)
    (hc : phi 25=phi 0)
    (h : ∀ i, i<25 → A+phi (i+1) ≤ B*count i+phi i) : 25*A ≤ 102*B := by
  have hs := potential_sum count phi A B 25 h
  rw [count_sum,hc] at hs
  norm_num at hs
  omega

/-- Any choice of a subset of zero credits has zero total credit. -/
theorem zero_credit_packing (credit : Nat → Nat) (J : Finset Nat)
    (h : ∀ i ∈ J, credit i=0) : (∑ i ∈ J, credit i)=0 := by
  exact Finset.sum_eq_zero h

/-- Even zero potential loss cannot exclude 235 at the recorded cycle ceiling. -/
theorem cannot_exclude_235 (num den loss : Nat) (h : 25*num ≤ 2448*den) :
    (num+840*den)*235 ≤ 219960*den+7*num+loss := by omega

#print axioms count_sum
#print axioms potential_sum
#print axioms cycle_mean_ceiling
#print axioms zero_credit_packing
#print axioms cannot_exclude_235
end Snake9.PackingLimit56
