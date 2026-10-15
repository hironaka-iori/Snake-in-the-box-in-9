import Aggregate247

namespace Snake9
open Finset
set_option maxHeartbeats 1200000

/-- Potential for sequences with neither 222 nor 223. This is a conditional
sequence statement and does not prove that a snake avoids 223. -/
def alpha223Potential (previous current : Nat) : Nat :=
  if current=1 then 3 else if current=2 then if previous=2 then 2 else 1 else 0

theorem alpha223Potential_step (x y z : Nat) (hy : 1≤y) (hz : 1≤z)
    (hy1 : y=1 → 4≤z) (hz1 : z=1 → 4≤y)
    (h222 : ¬(x=2 ∧ y=2 ∧ z=2)) (h223 : ¬(x=2 ∧ y=2 ∧ z=3)) :
    5+alpha223Potential x y ≤ 2*z+alpha223Potential y z := by
  unfold alpha223Potential
  split_ifs <;> omega

def alpha223PrefixPotential (f : Nat → Nat) (i : Nat) : Nat :=
  alpha223Potential (if i=0 then 0 else f (i-1)) (f i)

theorem alpha223PrefixPotential_step (f : Nat → Nat) (n i : Nat) (hi : i+1<n)
    (hpos : ∀j<n,1≤f j)
    (hone : ∀j,j+1<n → (f j=1 → 4≤f (j+1)) ∧ (f (j+1)=1 → 4≤f j))
    (h222 : ∀j,j+2<n → ¬(f j=2 ∧ f (j+1)=2 ∧ f (j+2)=2))
    (h223 : ∀j,j+2<n → ¬(f j=2 ∧ f (j+1)=2 ∧ f (j+2)=3)) :
    5+alpha223PrefixPotential f i ≤ 2*f (i+1)+alpha223PrefixPotential f (i+1) := by
  have ht (k : Nat) (hk : k=2 ∨ k=3) :
      ¬((if i=0 then 0 else f (i-1))=2 ∧ f i=2 ∧ f (i+1)=k) := by
    by_cases hi0 : i=0
    · simp [hi0]
    · have he1 : i-1+1=i := by omega
      have he2 : i-1+2=i+1 := by omega
      rcases hk with rfl | rfl
      · simpa only [if_neg hi0,he1,he2] using h222 (i-1) (by omega)
      · simpa only [if_neg hi0,he1,he2] using h223 (i-1) (by omega)
  have hs := alpha223Potential_step (if i=0 then 0 else f (i-1)) (f i) (f (i+1))
    (hpos i (by omega)) (hpos (i+1) hi) (hone i hi).1 (hone i hi).2
    (ht 2 (Or.inl rfl)) (ht 3 (Or.inr rfl))
  simpa [alpha223PrefixPotential] using hs

theorem alpha223_prefix_cost (f : Nat → Nat) (n : Nat) (hn : 1≤n)
    (hfirst : 4≤f 0) (hpos : ∀j<n,1≤f j)
    (hone : ∀j,j+1<n → (f j=1 → 4≤f (j+1)) ∧ (f (j+1)=1 → 4≤f j))
    (h222 : ∀j,j+2<n → ¬(f j=2 ∧ f (j+1)=2 ∧ f (j+2)=2))
    (h223 : ∀j,j+2<n → ¬(f j=2 ∧ f (j+1)=2 ∧ f (j+2)=3)) :
    5*n+3 ≤ 2*(∑j∈Finset.range n,f j)+alpha223PrefixPotential f (n-1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      simp only [Nat.zero_add,Finset.sum_range_one,Nat.add_sub_cancel]
      have hp : alpha223PrefixPotential f 0=0 := by
        simp [alpha223PrefixPotential,alpha223Potential,show f 0≠1 by omega,show f 0≠2 by omega]
      rw [hp]
      omega
    · have hprev := ih (by omega) (fun j hj => hpos j (by omega))
        (fun j hj => hone j (by omega)) (fun j hj => h222 j (by omega)) (fun j hj => h223 j (by omega))
      have hstep := alpha223PrefixPotential_step f (n+1) (n-1) (by omega) hpos hone h222 h223
      have he : n-1+1=n := by omega
      rw [he] at hstep
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel]
      omega

theorem alpha223_sequence_cost (f : Nat → Nat) (n : Nat) (hn : 1≤n)
    (hfirst : 4≤f 0) (hlast : 4≤f (n-1)) (hpos : ∀j<n,1≤f j)
    (hone : ∀j,j+1<n → (f j=1 → 4≤f (j+1)) ∧ (f (j+1)=1 → 4≤f j))
    (h222 : ∀j,j+2<n → ¬(f j=2 ∧ f (j+1)=2 ∧ f (j+2)=2))
    (h223 : ∀j,j+2<n → ¬(f j=2 ∧ f (j+1)=2 ∧ f (j+2)=3)) :
    5*n+3 ≤ 2*(∑j∈Finset.range n,f j) := by
  have hp : alpha223PrefixPotential f (n-1)=0 := by
    simp [alpha223PrefixPotential,alpha223Potential,show f (n-1)≠1 by omega,show f (n-1)≠2 by omega]
  have hs := alpha223_prefix_cost f n hn hfirst hpos hone h222 h223
  simpa only [hp,Nat.add_zero] using hs

#print axioms alpha223_sequence_cost
end Snake9
