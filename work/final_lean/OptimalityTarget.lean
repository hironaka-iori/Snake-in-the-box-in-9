import Snake9

namespace Snake9

theorem noNext_iff_upperBound (b : Nat) :
    (¬ Nonempty (Snake (b + 1))) ↔ (∀ m, Nonempty (Snake m) → m ≤ b) := by
  constructor
  · intro h m hp
    cases Nat.lt_or_ge m (b+1) with
    | inl hm => omega
    | inr hm =>
      obtain ⟨p⟩ := hp
      exact False.elim (h ⟨takePrefix p hm⟩)
  · intro h hp
    have := h (b+1) hp
    omega

/- A precise geometric statement of the sequence-based conjecture. -/
def Hypothesis196 : Prop :=
  Nonempty (Snake 196) ∧ (∀ m, Nonempty (Snake m) → m ≤ 196)

theorem hypothesis196_iff_witness_and_exclusion :
    Hypothesis196 ↔ Nonempty (Snake 196) ∧ ¬ Nonempty (Snake 197) := by
  unfold Hypothesis196
  rw [← noNext_iff_upperBound 196]

theorem witness196_implies_witness192 (h : Nonempty (Snake 196)) :
    Nonempty (Snake 192) := by
  obtain ⟨p⟩ := h
  exact ⟨takePrefix p (by decide : 192 ≤ 196)⟩

theorem hypothesis196_refutes_upper191 (h : Hypothesis196) :
    ¬ (∀ m, Nonempty (Snake m) → m ≤ 191) := by
  intro hb
  have := hb 196 h.1
  omega

#print axioms noNext_iff_upperBound
#print axioms hypothesis196_iff_witness_and_exclusion
#print axioms witness196_implies_witness192
#print axioms hypothesis196_refutes_upper191
end Snake9
