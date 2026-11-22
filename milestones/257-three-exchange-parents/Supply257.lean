import LayerJoining

namespace Supply257
open LayerJoining

variable {V : Type} {R : V → V → Prop} {m : Nat}

private theorem adjacent_indices (p : InducedPath V R m)
    (symm : ∀ x y, R x y → R y x) (irrefl : ∀ x, ¬ R x x)
    (i j : Fin (m+1)) (h : R (p.vertex i) (p.vertex j)) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  by_cases lt : i.val < j.val
  · exact Or.inl ((p.induced i j lt).mp h)
  by_cases gt : j.val < i.val
  · exact Or.inr ((p.induced j i gt).mp (symm _ _ h))
  have eq : i = j := Fin.ext (by omega)
  subst j
  exact (irrefl _ h).elim

/-- A selected vertex has at most two neighbours anywhere on the induced path. -/
theorem degree_two (p : InducedPath V R m)
    (symm : ∀ x y, R x y → R y x) (irrefl : ∀ x, ¬ R x x)
    (j a b c : Fin (m+1))
    (ha : R (p.vertex j) (p.vertex a)) (hb : R (p.vertex j) (p.vertex b))
    (hc : R (p.vertex j) (p.vertex c)) :
    a = b ∨ a = c ∨ b = c := by
  have h₁ := adjacent_indices p symm irrefl j a ha
  have h₂ := adjacent_indices p symm irrefl j b hb
  have h₃ := adjacent_indices p symm irrefl j c hc
  by_cases ab : a.val = b.val
  · exact Or.inl (Fin.ext ab)
  by_cases ac : a.val = c.val
  · exact Or.inr (Or.inl (Fin.ext ac))
  exact Or.inr (Or.inr (Fin.ext (by omega)))

/-- Before inserting u, each of its eventual two connector labels sees at most one old site. -/
theorem insertion_supply (p : InducedPath V R m)
    (symm : ∀ x y, R x y → R y x) (irrefl : ∀ x, ¬ R x x)
    (left u right : Fin (m+1)) (h₁ : left.val + 1 = u.val)
    (h₂ : u.val + 1 = right.val) (old : V → Prop)
    (subset : ∀ x, old x → ∃ j, p.vertex j = x) (fresh : ¬ old (p.vertex u)) :
    ∃ a b : V, a ≠ b ∧ R a (p.vertex u) ∧ R b (p.vertex u) ∧
      (∀ y, y = a ∨ y = b → ∀ x z, old x → old z → R y x → R y z → x = z) := by
  have hl : R (p.vertex left) (p.vertex u) :=
    (p.induced left u (by omega)).mpr h₁
  have hr : R (p.vertex right) (p.vertex u) :=
    symm _ _ ((p.induced u right (by omega)).mpr h₂)
  have distinct : p.vertex left ≠ p.vertex right := by
    intro eq
    have hi := congrArg Fin.val (p.distinct _ _ eq)
    omega
  have one (t : Fin (m+1)) (near : R (p.vertex t) (p.vertex u)) :
      ∀ x z, old x → old z → R (p.vertex t) x → R (p.vertex t) z → x = z := by
    intro x z hx hz ax az
    obtain ⟨i, rfl⟩ := subset x hx
    obtain ⟨j, rfl⟩ := subset z hz
    rcases degree_two p symm irrefl t i j u ax az near with ij | iu | ju
    · exact congrArg p.vertex ij
    · exact (fresh (iu ▸ hx)).elim
    · exact (fresh (ju ▸ hz)).elim
  refine ⟨p.vertex left, p.vertex right, distinct, hl, hr, ?_⟩
  intro y hy
  rcases hy with rfl | rfl
  · exact one left hl
  · exact one right hr

end Supply257
#print axioms Supply257.degree_two
#print axioms Supply257.insertion_supply
