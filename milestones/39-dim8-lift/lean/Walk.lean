import LocalWindowModel
/-! Sub-list glue for the cover certificates, on `Nat` literal codes (`decodeLit`).

`walkN full 0 core` checks, in one ordered pass over `full`, that every pair `(j, c)` of `core` (indices
strictly increasing) has `full[j] = c.map decodeLit`. Then `Unsat` of the core clauses gives `Unsat full`
(`unsat_of_walkN`). The data are `Nat` codes because `Int` literals are slow to elaborate. -/
namespace Dim8Lift.Walk
open Snake9.LocalWindow

def walkN : List (List Int) → Nat → List (Nat × List Nat) → Bool
  | _, _, [] => true
  | [], _, _ :: _ => false
  | f :: fs, i, (j, c) :: cs =>
    if i = j then (f == c.map decodeLit) && walkN fs (i + 1) cs
    else if i < j then walkN fs (i + 1) ((j, c) :: cs) else false

theorem walkN_mem : ∀ (full : List (List Int)) (i : Nat) (core : List (Nat × List Nat)), walkN full i core = true →
    ∀ p ∈ core, p.2.map decodeLit ∈ full
  | _, _, [], _, p, hp => by simp at hp
  | [], _, _ :: _, h, _, _ => by simp [walkN] at h
  | f :: fs, i, (j, c) :: cs, h, p, hp => by
    unfold walkN at h
    by_cases e : i = j
    · rw [if_pos e] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [h.1]
      · exact List.mem_cons_of_mem _ (walkN_mem fs (i + 1) cs h.2 p hp)
    · rw [if_neg e] at h
      by_cases l : i < j
      · rw [if_pos l] at h
        exact List.mem_cons_of_mem _ (walkN_mem fs (i + 1) ((j, c) :: cs) h p hp)
      · rw [if_neg l] at h; simp at h

theorem unsat_of_walkN (full : List (List Int)) (core : List (Nat × List Nat)) (h : walkN full 0 core = true)
    (hU : Unsat (core.map fun p => p.2.map decodeLit)) : Unsat full := by
  intro τ
  cases hf : cnfTrue τ full
  · rfl
  · exfalso
    have hc : cnfTrue τ (core.map fun p => p.2.map decodeLit) = true := by
      unfold cnfTrue at *
      rw [List.all_eq_true] at *
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact hf _ (walkN_mem full 0 core h p hp)
    rw [hU τ] at hc; exact absurd hc (by simp)

end Dim8Lift.Walk
