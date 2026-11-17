import Std

set_option Elab.async false

namespace ExchangeBalance236

private theorem filter_exchange_count {V : Type} (neighbours : List V)
    (before after : V → Bool) :
    (neighbours.filter before).length +
        (neighbours.filter (fun w => !before w && after w)).length =
      (neighbours.filter after).length +
        (neighbours.filter (fun w => before w && !after w)).length := by
  induction neighbours with
  | nil => simp
  | cons w rest ih =>
      cases hb : before w <;> cases ha : after w <;>
        simp [hb, ha] at * <;> omega

/-- Balance derived from the actual Boolean neighbour filters. At a retained
vertex the two degree hypotheses are supplied by the old and new paths. -/
theorem retained_degree_balance {V : Type} (neighbours : List V)
    (before after : V → Bool) (oldEndpoint newEndpoint : Nat)
    (oldDegree : (neighbours.filter before).length + oldEndpoint = 2)
    (newDegree : (neighbours.filter after).length + newEndpoint = 2) :
    (neighbours.filter (fun w => !before w && after w)).length + newEndpoint =
      (neighbours.filter (fun w => before w && !after w)).length + oldEndpoint := by
  have partition := filter_exchange_count neighbours before after
  omega

/-- An unchanged endpoint status forces equal numbers of added and removed
neighbours, including when the vertex is internal in both paths. -/
theorem unchanged_status_equal_counts {V : Type} (neighbours : List V)
    (before after : V → Bool) (endpoint : Nat)
    (oldDegree : (neighbours.filter before).length + endpoint = 2)
    (newDegree : (neighbours.filter after).length + endpoint = 2) :
    (neighbours.filter (fun w => !before w && after w)).length =
      (neighbours.filter (fun w => before w && !after w)).length := by
  have balance := retained_degree_balance neighbours before after endpoint endpoint
    oldDegree newDegree
  omega

/-- A retained old endpoint that becomes internal must acquire a new
neighbour, even if some of its old neighbours are removed. -/
theorem endpoint_becomes_internal {V : Type} (neighbours : List V)
    (before after : V → Bool)
    (oldDegree : (neighbours.filter before).length + 1 = 2)
    (newDegree : (neighbours.filter after).length = 2) :
    (neighbours.filter (fun w => !before w && after w)).length =
        (neighbours.filter (fun w => before w && !after w)).length + 1 ∧
      ∃ w, w ∈ neighbours ∧ before w = false ∧ after w = true := by
  have newDegree' : (neighbours.filter after).length + 0 = 2 := by omega
  have balance := retained_degree_balance neighbours before after 1 0
    oldDegree newDegree'
  have positive : 0 <
      (neighbours.filter (fun w => !before w && after w)).length := by omega
  constructor
  · omega
  · obtain ⟨w, member, changed⟩ := List.length_filter_pos_iff.mp positive
    refine ⟨w, member, ?_⟩
    cases hb : before w <;> cases ha : after w <;> simp_all

/-- At an internal vertex retained by both paths, an inserted neighbour
exists exactly when a removed neighbour exists. The stronger count equality
is unchanged_status_equal_counts with endpoint zero. -/
theorem internal_addition_iff_removal {V : Type} (neighbours : List V)
    (before after : V → Bool)
    (oldDegree : (neighbours.filter before).length = 2)
    (newDegree : (neighbours.filter after).length = 2) :
    (∃ w, w ∈ neighbours ∧ before w = false ∧ after w = true) ↔
      (∃ w, w ∈ neighbours ∧ before w = true ∧ after w = false) := by
  have equalCounts := unchanged_status_equal_counts neighbours before after 0
    (by omega) (by omega)
  have addedPositive :
      0 < (neighbours.filter (fun w => !before w && after w)).length ↔
        ∃ w, w ∈ neighbours ∧ before w = false ∧ after w = true := by
    rw [List.length_filter_pos_iff]
    constructor
    · rintro ⟨w, member, changed⟩
      refine ⟨w, member, ?_⟩
      cases hb : before w <;> cases ha : after w <;> simp_all
    · rintro ⟨w, member, oldFalse, newTrue⟩
      exact ⟨w, member, by simp [oldFalse, newTrue]⟩
  have removedPositive :
      0 < (neighbours.filter (fun w => before w && !after w)).length ↔
        ∃ w, w ∈ neighbours ∧ before w = true ∧ after w = false := by
    rw [List.length_filter_pos_iff]
    constructor
    · rintro ⟨w, member, changed⟩
      refine ⟨w, member, ?_⟩
      cases hb : before w <;> cases ha : after w <;> simp_all
    · rintro ⟨w, member, oldTrue, newFalse⟩
      exact ⟨w, member, by simp [oldTrue, newFalse]⟩
  constructor
  · intro added
    apply removedPositive.mp
    rw [← equalCounts]
    exact addedPositive.mpr added
  · intro removed
    apply addedPositive.mp
    rw [equalCounts]
    exact removedPositive.mpr removed

#print axioms retained_degree_balance
#print axioms unchanged_status_equal_counts
#print axioms endpoint_becomes_internal
#print axioms internal_addition_iff_removal

end ExchangeBalance236
