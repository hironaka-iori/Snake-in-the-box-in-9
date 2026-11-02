import CoverageAssembly

namespace Snake9.Shared89
open Snake9.Boxes88

/-- The three geometric witness constructors do not inspect the history. -/
def historyFree : Witness → Bool
  | .reference _ _ _ => true
  | .short _ _ _ => true
  | .interval _ _ _ => true
  | .history _ => false

def entriesHistoryFree (entries : List (Box × Witness)) : Bool :=
  entries.all fun item => historyFree item.2

/-- Validity transfers between bounded history indices when the witness does
not use the history constructor. Direction and box are unchanged. -/
theorem witness_valid_transport (q0 q di : Nat) (b : Box) (w : Witness)
    (hfree : historyFree w = true) (hq : q < 75)
    (hv : boxWitnessValid q0 di b w = true) :
    boxWitnessValid q di b w = true := by
  cases w with
  | history ki => simp [historyFree] at hfree
  | reference ki s reverse =>
    simp only [boxWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    exact ⟨⟨hv.1.1,hq,hv.1.2.2⟩,hv.2⟩
  | short ki s reverse =>
    simp only [boxWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    exact ⟨⟨hv.1.1,hq,hv.1.2.2⟩,hv.2⟩
  | interval ki s reverse =>
    simp only [boxWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    exact ⟨⟨hv.1.1,hq,hv.1.2.2⟩,hv.2⟩

/-- In particular, setting q0 to zero reuses a checked geometric base list. -/
theorem entries_valid_transport (q0 q di : Nat) (entries : List (Box × Witness))
    (hfree : entriesHistoryFree entries = true) (hq : q < 75)
    (hv : entriesValid q0 di entries = true) : entriesValid q di entries = true := by
  apply List.all_eq_true.mpr
  intro item hm
  exact witness_valid_transport q0 q di item.1 item.2
    (List.all_eq_true.mp hfree item hm) hq (List.all_eq_true.mp hv item hm)

theorem entries_valid_append (q di : Nat) (base extra : List (Box × Witness))
    (hb : entriesValid q di base = true) (he : entriesValid q di extra = true) :
    entriesValid q di (base ++ extra) = true := by
  change ((base ++ extra).all fun item => boxWitnessValid q di item.1 item.2) = true
  rw [List.all_append]
  exact Bool.and_eq_true_iff.mpr ⟨hb,he⟩

/-- A separately checked history witness can be added to the shared base.
This statement does not assert the existence or uniqueness of that witness. -/
theorem base_plus_history_valid (q di : Nat) (base : List (Box × Witness))
    (b : Box) (ki : Nat) (hq : q < 75)
    (hfree : entriesHistoryFree base = true)
    (hb : entriesValid 0 di base = true)
    (hh : boxWitnessValid q di b (.history ki) = true) :
    entriesValid q di (base ++ [(b, .history ki)]) = true := by
  apply entries_valid_append q di base [(b, .history ki)]
  · exact entries_valid_transport 0 q di base hfree hq hb
  · simpa only [entriesValid, List.all_cons, List.all_nil, Bool.and_true] using hh

#print axioms witness_valid_transport
#print axioms entries_valid_transport
#print axioms entries_valid_append
#print axioms base_plus_history_valid
end Snake9.Shared89
