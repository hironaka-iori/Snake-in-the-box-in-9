import Std

namespace ParityWitness

/-- Opposite-parity vertex w has exactly the two specified neighbours in a fixed set S. -/
def Witness {α β : Type} (edge : α → β → Prop) (S : α → Prop)
    (a b : α) (w : β) : Prop :=
  ∀ x, S x → (edge x w ↔ x = a ∨ x = b)

theorem witnessPairs {α β : Type} {edge : α → β → Prop} {S : α → Prop}
    {a b c d : α} {w : β}
    (ha : S a) (hb : S b) (hne : a ≠ b)
    (one : Witness edge S a b w) (two : Witness edge S c d w) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have aa : edge a w := (one a ha).mpr (Or.inl rfl)
  have bb : edge b w := (one b hb).mpr (Or.inr rfl)
  rcases (two a ha).mp aa with ac | ad
  · rcases (two b hb).mp bb with bc | bd
    · exact False.elim (hne (ac.trans bc.symm))
    · exact Or.inl ⟨ac, bd⟩
  · rcases (two b hb).mp bb with bc | bd
    · exact Or.inr ⟨ad, bc⟩
    · exact False.elim (hne (ad.trans bd.symm))

/-- All endpoints and all intermediates at once, with no finite-size restriction. -/
theorem exactIncidence {ι κ α β : Type} {edge : α → β → Prop}
    {x : ι → α} {w : κ → β} {left right : κ → ι}
    (injective : ∀ {u v}, x u = x v → u = v)
    (witness : ∀ j, Witness edge (fun a => ∃ i, x i = a)
                              (x (left j)) (x (right j)) (w j)) :
    ∀ i j, edge (x i) (w j) ↔ i = left j ∨ i = right j := by
  intro i j
  constructor
  · intro h
    rcases (witness j (x i) ⟨i,rfl⟩).mp h with h₁ | h₂
    · exact Or.inl (injective h₁)
    · exact Or.inr (injective h₂)
  · intro h
    apply (witness j (x i) ⟨i,rfl⟩).mpr
    rcases h with h₁ | h₂
    · exact Or.inl (congrArg x h₁)
    · exact Or.inr (congrArg x h₂)

theorem separateWitnesses {α β : Type} {edge : α → β → Prop} {S : α → Prop}
    {a b c d : α} {u v : β} (ha : S a) (hb : S b) (hne : a ≠ b)
    (hu : Witness edge S a b u) (hv : Witness edge S c d v)
    (distinct : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) : u ≠ v := by
  intro h
  subst v
  exact distinct (witnessPairs ha hb hne hu hv)

#print axioms witnessPairs
#print axioms exactIncidence
#print axioms separateWitnesses
end ParityWitness
