import ColourContraction231

set_option Elab.async false

namespace ContractedDegrees237
open LayerJoining ColourContraction231

/-- Two distinct vertices among the even path positions have a common
label whose neighbours among those positions are precisely these two. -/
def Partner {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2 * k)) (a b : Nat) : Prop :=
  a ≤ k ∧ b ≤ k ∧ a ≠ b ∧ ∃ z : V, ∀ i : Fin (k + 1),
    R (p.vertex ⟨2 * i.val, by have h := i.isLt; omega⟩) z ↔
      i.val = a ∨ i.val = b

theorem partner_symmetric {V : Type} {R : V → V → Prop} {k : Nat}
    {p : InducedPath V R (2 * k)} {a b : Nat} :
    Partner p a b → Partner p b a := by
  rintro ⟨ha, hb, ab, z, hz⟩
  exact ⟨hb, ha, Ne.symm ab, z, fun i => (hz i).trans or_comm⟩

/-- The actual label at odd position 2i+1 witnesses the edge.
Any other label witnessing the same edge does not change the partner. -/
theorem consecutive_partners {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2 * k)) (sym : ∀ v w, R v w → R w v)
    (i : Nat) (hi : i < k) : Partner p i (i + 1) := by
  refine ⟨by omega, by omega, by omega, p.vertex ⟨2 * i + 1, by omega⟩, ?_⟩
  intro j
  exact even_odd_adjacency p sym j ⟨i, hi⟩

section Order

variable {G : Nat → Nat → Prop} {k : Nat}

def AtMostOne (G : Nat → Nat → Prop) (v : Nat) : Prop :=
  ∀ a b, G v a → G v b → a = b

def AtMostTwo (G : Nat → Nat → Prop) (v : Nat) : Prop :=
  ∀ a b c, G v a → G v b → G v c → a = b ∨ a = c ∨ b = c

variable (sym : ∀ {a b}, G a b → G b a)
  (steps : ∀ j, j < k → G j (j+1))

include sym steps

theorem no_isolate (nontrivial : 0 < k) (v : Nat) (hv : v ≤ k) :
    ∃ u, u ≠ v ∧ G v u := by
  by_cases last : v < k
  · exact ⟨v+1, by omega, steps v last⟩
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show v ≠ 0 by omega)
    exact ⟨t, by omega, sym (steps t (by omega))⟩

theorem leaf_at_end (v : Nat) (hv : v ≤ k) (leaf : AtMostOne G v) :
    v = 0 ∨ v = k := by
  by_cases zero : v = 0
  · exact Or.inl zero
  by_cases last : v = k
  · exact Or.inr last
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero zero
  have eq := leaf t (t+1+1) (sym (steps t (by omega))) (steps (t+1) (by omega))
  omega

/-- Every neighbour of an interior vertex of degree at most two is used.
In particular every unused edge at such a low-degree vertex forces it to
be an endpoint in every ordering. -/
theorem low_neighbour_positions {u v : Nat} (hu : u ≤ k)
    (low : AtMostTwo G u) (edge : G v u) :
    u = 0 ∨ u = k ∨ u+1 = v ∨ v+1 = u := by
  by_cases zero : u = 0
  · exact Or.inl zero
  by_cases last : u = k
  · exact Or.inr (Or.inl last)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero zero
  have eq := low t (t+1+1) v (sym (steps t (by omega))) (steps (t+1) (by omega)) (sym edge)
  omega

theorem not_five_low_neighbours {v a b c d e : Nat}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) (he : e ≤ k)
    (lb : AtMostTwo G b) (lc : AtMostTwo G c) (ld : AtMostTwo G d)
    (eb : G v b) (ec : G v c) (ed : G v d) : False := by
  have hb := low_neighbour_positions sym steps (by omega : b ≤ k) lb eb
  have hc := low_neighbour_positions sym steps (by omega : c ≤ k) lc ec
  have hd := low_neighbour_positions sym steps (by omega : d ≤ k) ld ed
  omega

theorem not_three_leaves {a b c : Nat} (hab : a < b) (hbc : b < c)
    (hc : c ≤ k) (middleLeaf : AtMostOne G b) : False := by
  have hb := leaf_at_end sym steps b (by omega) middleLeaf
  omega

theorem leaf_edge_used {u v : Nat} (hu : u ≤ k) (positive : 0 < k)
    (leaf : AtMostOne G u) (edge : G v u) : u+1 = v ∨ v+1 = u := by
  by_cases h : u < k
  · exact Or.inl (leaf _ _ (steps u h) (sym edge))
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show u ≠ 0 by omega)
    have eq := leaf i v (sym (steps i (by omega))) (sym edge)
    omega

/-- When two leaves already occupy the two endpoints, every edge incident
with any vertex of degree at most two belongs to the Hamiltonian path. -/
theorem low_edge_used_with_two_leaves {u v a b : Nat} (hu : u ≤ k)
    (ha : a ≤ k) (hb : b ≤ k) (ab : a ≠ b)
    (la : AtMostOne G a) (lb : AtMostOne G b)
    (low : AtMostTwo G u) (edge : G v u) : u+1 = v ∨ v+1 = u := by
  have ea := leaf_at_end sym steps a ha la
  have eb := leaf_at_end sym steps b hb lb
  have pos : 0 < k := by omega
  by_cases eqA : u = a
  · subst u
    exact leaf_edge_used sym steps ha pos la edge
  by_cases eqB : u = b
  · subst u
    exact leaf_edge_used sym steps hb pos lb edge
  have p := low_neighbour_positions sym steps hu low edge
  omega

end Order

#print axioms consecutive_partners
#print axioms no_isolate
#print axioms leaf_at_end
#print axioms low_neighbour_positions
#print axioms not_five_low_neighbours
#print axioms not_three_leaves
#print axioms leaf_edge_used
#print axioms low_edge_used_with_two_leaves

end ContractedDegrees237
