import Mathlib.Tactic
namespace Snake9.CriticalFamily61

theorem path_bound (p d : Nat) (pi f w : Nat → Nat) : ∀ n,
    (∀ i<n, p+pi (f (i+1)) ≤ d*w i+pi (f i)) →
    n*p+pi (f n) ≤ d*(∑ i ∈ Finset.range n, w i)+pi (f 0) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have hprev := ih (by intro i hi; exact h i (by omega))
    have hlast := h n (by omega)
    simp only [Finset.sum_range_succ,Nat.succ_mul,Nat.mul_add]
    omega

theorem closed_bound (p d n : Nat) (pi f w : Nat → Nat)
    (h : ∀ i<n, p+pi (f (i+1)) ≤ d*w i+pi (f i)) (hc : f n=f 0) :
    n*p ≤ d*(∑ i ∈ Finset.range n, w i) := by
  have := path_bound p d pi f w n h
  rw [hc] at this
  omega

def checkEdges (p d : Nat) (pi : List Nat) (es : List (Nat × Nat × Nat)) : Bool :=
  es.all fun e => decide (p+pi.getD e.2.1 0 ≤ d*e.2.2+pi.getD e.1 0)

theorem edge_of_check {p d : Nat} {pi : List Nat} {es : List (Nat × Nat × Nat)}
    (h : checkEdges p d pi es=true) {u v w : Nat} (he : (u,v,w)∈es) :
    p+pi.getD v 0 ≤ d*w+pi.getD u 0 :=
  of_decide_eq_true (List.all_eq_true.mp h (u,v,w) he)

#print axioms path_bound
#print axioms closed_bound
#print axioms edge_of_check
end Snake9.CriticalFamily61
