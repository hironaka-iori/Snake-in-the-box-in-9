import Mathlib.Tactic

namespace Snake9.PairCapacity134
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem anchor_card_le_eight (q : Fin 9) (A : Finset (Fin 9)) (hq : q ∉ A) :
    A.card ≤ 8 := by
  have hsub : A ⊆ Finset.univ.erase q := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨by intro he; exact hq (he ▸ ha),Finset.mem_univ a⟩
  have h := Finset.card_le_card hsub
  simpa using h

theorem incident_pair_card : ∀ (q : Fin 9) (A : Finset (Fin 9)), q ∉ A →
    ((Finset.univ : Finset (Fin 9 × Fin 9)).filter (fun ab =>
      ab.1 < ab.2 ∧ ab.1 ≠ q ∧ ab.2 ≠ q ∧
        (ab.1 ∈ A ∨ ab.2 ∈ A))).card =
      7*A.card - A.card*(A.card-1)/2 := by
  decide +kernel

theorem pair_values_injective : ∀ a b c d : Fin 9, a < b → c < d →
    (2^a.val ^^^ 2^b.val) = (2^c.val ^^^ 2^d.val) → a=c ∧ b=d := by
  decide +kernel

theorem selected_and_missing_card (q : Fin 9) (A : Finset (Fin 9)) (hq : q ∉ A)
    (selected : (Fin 9 × Fin 9) → Prop) [DecidablePred selected] :
    let U := (Finset.univ : Finset (Fin 9 × Fin 9)).filter (fun ab =>
      ab.1 < ab.2 ∧ ab.1 ≠ q ∧ ab.2 ≠ q ∧ (ab.1 ∈ A ∨ ab.2 ∈ A))
    (U.filter selected).card + (U.filter (fun ab => ¬ selected ab)).card =
      7*A.card - A.card*(A.card-1)/2 := by
  dsimp only
  rw [Finset.filter_card_add_filter_neg_card_eq_card]
  exact incident_pair_card q A hq

#print axioms anchor_card_le_eight
#print axioms incident_pair_card
#print axioms pair_values_injective
#print axioms selected_and_missing_card
end Snake9.PairCapacity134
