import LocalWindowModel

namespace Snake9.LocalWindow

def selectedClauses (F : List (List Int)) (ids : List Nat) : List (List Int) :=
  ids.map (fun i => F.getD i [])

theorem selectedClauses_subset {F : List (List Int)} {ids : List Nat}
    (hv : ids.all (fun i => decide (i < F.length)) = true) :
    ∀ c ∈ selectedClauses F ids, c ∈ F := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  have hi' : i < F.length := of_decide_eq_true (List.all_eq_true.1 hv i hi)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  exact List.getElem_mem _

/-- A refutation of a checked subset refutes the complete geometric core. -/
theorem unsat_of_selected {F : List (List Int)} {ids : List Nat}
    (hv : ids.all (fun i => decide (i < F.length)) = true)
    (hu : Unsat (selectedClauses F ids)) : Unsat F := by
  intro tau
  cases he : cnfTrue tau F
  · rfl
  · exfalso
    have hall : cnfTrue tau (selectedClauses F ids) = true := by
      apply List.all_eq_true.2
      intro c hc
      exact List.all_eq_true.1 he c (selectedClauses_subset hv c hc)
    rw [hu tau] at hall
    exact Bool.false_ne_true hall

#print axioms unsat_of_selected
end Snake9.LocalWindow
