import LocalWindowBridge

namespace Snake9.PairRepresentation134
open Snake9.LocalWindow

theorem first_neighbour_indices {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (j : Nat) (hj : j ≤ m) (hadj : vx p j ∈ nbrs (vx p 1)) :
    j=0 ∨ j=2 := by
  have h := (vx_adj_iff p hm hj).mp ((mem_nbrs _ _).mp hadj)
  omega

theorem unselected_neighbour_coordinate {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q z : Nat) (hzero : vx p 0 = 0) (hfirst : vx p 1 = 2^q)
    (hnot : sel p (fun v => v) z = false) (hadj : vx p 0 ∈ nbrs z) :
    ∃ a, a < 9 ∧ a ≠ q ∧ z = 2^a := by
  obtain ⟨a,ha,he⟩ := (mem_nbrs _ _).mp hadj
  rw [hzero] at he
  have hz : z = 2^a := by
    have hx := congrArg (fun w => w ^^^ 2^a) he
    simpa only [Nat.zero_xor,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero] using hx.symm
  refine ⟨a,ha,?_,hz⟩
  intro heq
  have hs : sel p (fun v => v) z = true := by
    apply (sel_iff p (fun v => v) z).mpr
    exact ⟨1,hm,by simpa only [hz,heq] using hfirst⟩
  rw [hnot] at hs
  exact Bool.false_ne_true hs

theorem selected_neighbour_pairs {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q a j : Nat) (ha : a < 9) (haq : a ≠ q)
    (hzero : vx p 0 = 0) (hfirst : vx p 1 = 2^q)
    (hj : j ≤ m) (hadj : vx p j ∈ nbrs (2^a)) :
    j=0 ∨ j=2 ∨ ∃ b, b < 9 ∧ b ≠ a ∧ b ≠ q ∧
      vx p j = 2^a ^^^ 2^b := by
  by_cases hj0 : j=0
  · exact Or.inl hj0
  by_cases hj2 : j=2
  · exact Or.inr (Or.inl hj2)
  obtain ⟨b,hb,he⟩ := (mem_nbrs _ _).mp hadj
  have hba : b ≠ a := by
    intro heq
    have hv : vx p j = vx p 0 := by
      rw [hzero,he,heq,Nat.xor_self]
    exact hj0 (vx_inj p hj (by omega) hv)
  have hbq : b ≠ q := by
    intro heq
    have hneighbour : vx p j ∈ nbrs (vx p 1) := by
      apply (mem_nbrs _ _).mpr
      refine ⟨a,ha,?_⟩
      rw [hfirst,he,heq,Nat.xor_comm]
    rcases first_neighbour_indices p hm j hj hneighbour with hz | ht
    · exact hj0 hz
    · exact hj2 ht
  exact Or.inr (Or.inr ⟨b,hb,hba,hbq,he⟩)

theorem selected_first_coordinate_pair {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q b j : Nat) (hb : b < 9) (hbq : b ≠ q)
    (hzero : vx p 0 = 0) (hfirst : vx p 1 = 2^q)
    (hj : j ≤ m) (he : vx p j = 2^q ^^^ 2^b) : j=2 := by
  have hadj : vx p j ∈ nbrs (vx p 1) := by
    apply (mem_nbrs _ _).mpr
    exact ⟨b,hb,by simpa only [hfirst] using he⟩
  rcases first_neighbour_indices p hm j hj hadj with hz | ht
  · subst j
    rw [hzero] at he
    have hx := congrArg (fun w => 2^q ^^^ w) he
    have hp : 2^q = 2^b := by
      simpa only [Nat.xor_zero,← Nat.xor_assoc,Nat.xor_self,Nat.zero_xor] using hx
    exact False.elim (hbq (pow_two_inj hp).symm)
  · exact ht

#print axioms first_neighbour_indices
#print axioms unselected_neighbour_coordinate
#print axioms selected_neighbour_pairs
#print axioms selected_first_coordinate_pair
end Snake9.PairRepresentation134
