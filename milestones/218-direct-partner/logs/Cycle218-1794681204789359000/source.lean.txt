import CycleCut196

set_option Elab.async false

namespace Cycle218
open LayerJoining

/-- Distinct cyclically ordered vertices cannot all occur in an induced path.
The relation is symmetric; the cycle has at least three vertices. -/
theorem cycle_not_contained {V : Type} {R : V → V → Prop} {m n : Nat}
    (p : InducedPath V R m) (c : Fin (n + 3) → V)
    (distinct : ∀ i j, c i = c j → i = j)
    (symmetric : ∀ u v, R u v → R v u)
    (step : ∀ i j : Fin (n + 3), i.val + 1 = j.val → R (c i) (c j))
    (closing : R (c ⟨n + 2, by omega⟩) (c ⟨0, by omega⟩)) :
    ¬ (∀ i, ∃ j, p.vertex j = c i) := by
  let prev : Fin (n + 3) → Fin (n + 3) := fun i =>
    ⟨if i.val = 0 then n + 2 else i.val - 1, by split <;> omega⟩
  let next : Fin (n + 3) → Fin (n + 3) := fun i =>
    ⟨if i.val + 1 < n + 3 then i.val + 1 else 0, by split <;> omega⟩
  have neighbours : ∀ i, c (prev i) ≠ c i ∧ c (next i) ≠ c i ∧
      c (prev i) ≠ c (next i) := by
    intro i
    have hidx : (prev i).val ≠ i.val ∧ (next i).val ≠ i.val ∧
        (prev i).val ≠ (next i).val := by
      have hp : (prev i).val = if i.val = 0 then n + 2 else i.val - 1 := rfl
      have hn : (next i).val = if i.val + 1 < n + 3 then i.val + 1 else 0 := rfl
      have bound := i.isLt
      split at hp <;> split at hn <;> omega
    constructor
    · intro h
      exact hidx.1 (congrArg Fin.val (distinct _ _ h))
    · constructor
      · intro h
        exact hidx.2.1 (congrArg Fin.val (distinct _ _ h))
      · intro h
        exact hidx.2.2 (congrArg Fin.val (distinct _ _ h))
  have edges : ∀ i, R (c (prev i)) (c i) ∧ R (c (next i)) (c i) := by
    intro i
    constructor
    · by_cases hz : i.val = 0
      · have hi : i = (⟨0, Nat.zero_lt_succ (n + 2)⟩ : Fin (n + 3)) := Fin.ext hz
        have hp : prev i = (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3)) := by
          apply Fin.ext
          simp only [prev, hz, if_true]
        rw [hp, hi]
        exact closing
      · apply step
        simp only [prev, hz, if_false]
        omega
    · apply symmetric
      by_cases ht : i.val + 1 < n + 3
      · apply step
        simp only [next, ht, if_true]
      · have hi : i = (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3)) := by
          apply Fin.ext
          change i.val = n + 2
          omega
        have hn : next i = (⟨0, Nat.zero_lt_succ (n + 2)⟩ : Fin (n + 3)) := by
          apply Fin.ext
          simp only [next, ht, if_false]
        rw [hn, hi]
        exact closing
  exact CycleCut196.noContainedDegreeTwo p c prev next neighbours edges

private theorem count_true_le (xs : List Bool) : xs.count true ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons b bs ih => cases b <;> simp_all <;> omega

private theorem count_true_lt_of_false (xs : List Bool) (h : false ∈ xs) :
    xs.count true < xs.length := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
      cases b with
      | false =>
          have hc := count_true_le bs
          simp_all
          omega
      | true =>
          have hm : false ∈ bs := by simpa using h
          have hc := ih hm
          simpa using hc

/-- Every selection drawn from the vertices of an actual induced path obeys
the cardinality cut for a distinct cycle in the ambient graph. -/
theorem cycle_cut {V : Type} {R : V → V → Prop} {m n : Nat}
    (p : InducedPath V R m) (c : Fin (n + 3) → V)
    (distinct : ∀ i j, c i = c j → i = j)
    (symmetric : ∀ u v, R u v → R v u)
    (step : ∀ i j : Fin (n + 3), i.val + 1 = j.val → R (c i) (c j))
    (closing : R (c ⟨n + 2, by omega⟩) (c ⟨0, by omega⟩))
    (selected : V → Bool)
    (fits : ∀ i, selected (c i) = true → ∃ j, p.vertex j = c i) :
    (List.ofFn (fun i => selected (c i))).count true ≤ n + 2 := by
  classical
  have missing : ∃ i, selected (c i) = false := by
    apply Classical.byContradiction
    intro h
    apply cycle_not_contained p c distinct symmetric step closing
    intro i
    apply fits i
    cases hs : selected (c i) with
    | false => exact False.elim (h ⟨i, hs⟩)
    | true => rfl
  obtain ⟨i, hi⟩ := missing
  have hm : false ∈ List.ofFn (fun i => selected (c i)) := by
    apply List.mem_ofFn.mpr
    exact ⟨i, hi⟩
  have hc := count_true_lt_of_false (List.ofFn (fun i => selected (c i))) hm
  simp only [List.length_ofFn] at hc
  omega

#print axioms cycle_not_contained
#print axioms cycle_cut
end Cycle218
