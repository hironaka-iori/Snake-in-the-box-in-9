import ReferenceInterface

/-!
Conditional consequences of a universal lower bound on six consecutive
internal counts. The local lower bound is an explicit hypothesis throughout.
The disjoint-block argument uses no claim from the pattern-specific probes.
-/
namespace Snake9.UniformSix124
open Finset
open scoped BigOperators

set_option maxHeartbeats 2000000

theorem disjoint_six_blocks (alpha : Nat → Nat) (B L : Nat)
    (hblocks : ∀ b < B, L ≤ ∑ j ∈ range 6, alpha (6*b+j+1)) :
    B*L ≤ ∑ i ∈ range (6*B), alpha (i+1) := by
  revert hblocks
  induction B with
  | zero =>
      intro _
      simp
  | succ B ih =>
      intro hblocks
      have hprev : B*L ≤ ∑ i ∈ range (6*B), alpha (i+1) :=
        ih (by intro b hb; exact hblocks b (by omega))
      have hlast : L ≤ ∑ j ∈ range 6, alpha (6*B+j+1) :=
        hblocks B (by omega)
      rw [Nat.succ_mul, Nat.mul_succ, Finset.sum_range_add]
      exact Nat.add_le_add hprev hlast

theorem total_lower_of_six_floor (alpha : Nat → Nat) (m B L : Nat)
    (hm : 6*B+1 ≤ m)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      L ≤ ∑ j ∈ range 6, alpha (r+j)) :
    B*L+(m-(6*B+1))+8 ≤ ∑ i ∈ range (m+1), alpha i := by
  have hblocks : B*L ≤ ∑ i ∈ range (6*B), alpha (i+1) := by
    apply disjoint_six_blocks
    intro b hb
    have h := hfloor (6*b+1) (by omega) (by omega)
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hrest : m-(6*B+1) ≤
      ∑ j ∈ range (m-(6*B+1)), alpha (6*B+j+1) := by
    calc
      _ = ∑ _j ∈ range (m-(6*B+1)), (1 : Nat) := by simp
      _ ≤ _ := Finset.sum_le_sum (by
        intro j hj
        have h := Finset.mem_range.mp hj
        exact hpos (6*B+j+1) (by omega) (by omega))
  have hsplit := Finset.sum_range_add (fun i => alpha (i+1))
    (6*B) (m-(6*B+1))
  have hlen : 6*B+(m-(6*B+1)) = m-1 := by omega
  rw [hlen] at hsplit
  have hp := Finset.sum_range_succ' alpha (m-1)
  have hm1 : m-1+1 = m := by omega
  rw [hm1] at hp
  have hpath : (∑ i ∈ range (m+1), alpha i) =
      alpha 0+(∑ i ∈ range (m-1), alpha (i+1))+alpha m := by
    rw [Finset.sum_range_succ, hp]
    omega
  omega

theorem bound233_of_floor26 (alpha : Nat → Nat) (m : Nat)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      26 ≤ ∑ j ∈ range 6, alpha (r+j))
    (hsquare : (∑ i ∈ range (m+1), alpha i)+35*(m+1) ≤ 9214) :
    m ≤ 233 := by
  by_contra h
  have hm : 234 ≤ m := by omega
  have ht := total_lower_of_six_floor alpha m 38 26
    (by omega) h0 hend hpos hfloor
  norm_num at ht
  omega

theorem bound234_of_floor25 (alpha : Nat → Nat) (m : Nat)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      25 ≤ ∑ j ∈ range 6, alpha (r+j))
    (hsquare : (∑ i ∈ range (m+1), alpha i)+35*(m+1) ≤ 9214) :
    m ≤ 234 := by
  by_contra h
  have hm : 235 ≤ m := by omega
  have ht := total_lower_of_six_floor alpha m 38 25
    (by omega) h0 hend hpos hfloor
  norm_num at ht
  omega

#print axioms disjoint_six_blocks
#print axioms total_lower_of_six_floor
#print axioms bound233_of_floor26
#print axioms bound234_of_floor25
end Snake9.UniformSix124
