import Std

namespace Compatibility263

variable {Parent Site : Type}

/-- A selected set avoids one member of a family exactly when it contains
    no set meeting every member. The common forbidden sites are handled separately. -/
theorem avoid_iff_no_transversal (extra : Parent → Site → Prop) (used : Site → Prop) :
    (∃ p, ∀ x, extra p x → ¬ used x) ↔
      ¬ ∃ T : Site → Prop, (∀ x, T x → used x) ∧ ∀ p, ∃ x, T x ∧ extra p x := by
  classical
  constructor
  · rintro ⟨p, hp⟩ ⟨T, hT, hits⟩
    obtain ⟨x, hx, he⟩ := hits p
    exact hp x he (hT x hx)
  · intro noT
    apply Classical.byContradiction
    intro h
    apply noT
    refine ⟨used, fun _ hx => hx, ?_⟩
    intro p
    apply Classical.byContradiction
    intro missing
    apply h
    refine ⟨p, ?_⟩
    intro x he hu
    exact missing ⟨x, hu, he⟩

/-- A previously certified necessary hit survives removal of currently forbidden sites. -/
theorem remaining_hit (used old blocked : Site → Prop)
    (mustHit : ∃ x, used x ∧ old x) (avoids : ∀ x, blocked x → ¬ used x) :
    ∃ x, used x ∧ old x ∧ ¬ blocked x := by
  obtain ⟨x, hu, ho⟩ := mustHit
  exact ⟨x, hu, ho, fun hb => avoids x hb hu⟩

/-- A common-core exclusion rules out every parent containing that core. -/
theorem subset_obstruction (used core parent : Site → Prop)
    (contains : ∀ x, core x → parent x) (mustHit : ∃ x, used x ∧ core x) :
    ¬ (∀ x, parent x → ¬ used x) := by
  obtain ⟨x, hu, hc⟩ := mustHit
  exact fun avoids => avoids x (contains x hc) hu

end Compatibility263

#print axioms Compatibility263.avoid_iff_no_transversal
#print axioms Compatibility263.remaining_hit
#print axioms Compatibility263.subset_obstruction
