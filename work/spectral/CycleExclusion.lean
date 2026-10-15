import PathStructure
import Mathlib.Tactic

namespace Snake9.CycleExclusion
open Finset
set_option maxHeartbeats 1000000

/-- Every nonempty finite subset of a snake has a vertex with at most one
neighbor inside that subset. This excludes cycles of every length. -/
theorem subset_has_low_degree {m : Nat} (p : Snake m) (s : Finset Vertex)
    (hne : s.Nonempty) (hselected : ∀ v ∈ s, InPath p v) :
    ∃ v ∈ s, ∀ a ∈ s, ∀ b ∈ s, Adj v a → Adj v b → a = b := by
  classical
  let indices := univ.filter (fun i : Fin (m + 1) => p.vertex i ∈ s)
  have hi : indices.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    obtain ⟨i, rfl⟩ := hselected v hv
    exact ⟨i, by simp [indices, hv]⟩
  let i := indices.min' hi
  have himem : i ∈ indices := min'_mem indices hi
  have hiv : p.vertex i ∈ s := (mem_filter.mp himem).2
  refine ⟨p.vertex i, hiv, ?_⟩
  intro a ha b hb hia hib
  obtain ⟨j, rfl⟩ := hselected a ha
  obtain ⟨k, rfl⟩ := hselected b hb
  have hjmem : j ∈ indices := by simp [indices, ha]
  have hkmem : k ∈ indices := by simp [indices, hb]
  have hij : i ≤ j := min'_le indices j hjmem
  have hik : i ≤ k := min'_le indices k hkmem
  have hja := (path_adj_iff p i j).mp hia
  have hka := (path_adj_iff p i k).mp hib
  have he : j.val = k.val := by
    change i.val ≤ j.val at hij
    change i.val ≤ k.val at hik
    omega
  exact congrArg p.vertex (Fin.ext he)

/-- A finite set with two distinct internal neighbors at every vertex cannot
be contained in any snake. Connectedness is unnecessary. -/
theorem two_neighbor_set_not_selected {m : Nat} (p : Snake m) (s : Finset Vertex)
    (hne : s.Nonempty)
    (hdegree : ∀ v ∈ s, ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ Adj v a ∧ Adj v b) :
    ¬ (∀ v ∈ s, InPath p v) := by
  intro hs
  obtain ⟨v, hv, hlow⟩ := subset_has_low_degree p s hne hs
  obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := hdegree v hv
  exact hab (hlow a ha b hb hva hvb)

def cycleCheck (c : List Vertex) : Bool :=
  !c.isEmpty && c.all (fun v => c.any (fun a => c.any (fun b =>
    decide (a ≠ b) && decide (Adj v a) && decide (Adj v b))))

theorem cycleCheck_sound (c : List Vertex) (h : cycleCheck c = true) :
    c ≠ [] ∧ ∀ v ∈ c, ∃ a ∈ c, ∃ b ∈ c, a ≠ b ∧ Adj v a ∧ Adj v b := by
  simpa [cycleCheck, and_assoc] using h

def recordedCycles : List (List Vertex) := [
  [48, 49, 50, 51],
  [68, 70, 71, 72, 73, 75, 76, 192, 193, 194, 197, 199, 202, 203],
  [80, 81, 82, 83],
  [96, 97, 98, 99],
  [260, 262, 263, 264, 265, 267, 268, 384, 385, 386, 389, 391, 394, 395],
  [272, 273, 274, 275],
  [288, 289, 290, 291],
  [320, 321, 322, 323],
  [0, 1, 2, 5, 10, 132, 133, 136, 138, 140],
  [36, 38, 40, 41, 44, 160, 161, 162, 166, 169],
  [144, 145, 146, 147],
  [192, 193, 194, 195],
  [384, 385, 386, 387],
  [0, 1, 2, 5, 10, 13, 14, 15],
  [19, 20, 22, 23, 24, 25, 27, 28],
  [35, 36, 38, 39, 40, 41, 43, 44],
  [67, 68, 70, 71, 72, 73, 75, 76],
  [131, 132, 134, 135, 136, 137, 139, 140],
  [259, 260, 262, 263, 264, 265, 267, 268],
  [0, 1, 2, 5, 10, 68, 69, 72, 74, 76],
  [36, 38, 40, 41, 44, 96, 97, 98, 102, 105],
  [132, 134, 136, 137, 140, 192, 193, 194, 198, 201],
  [260, 262, 264, 265, 268, 320, 321, 322, 326, 329],
  [20, 22, 23, 24, 25, 27, 28, 31],
  [36, 38, 39, 40, 41, 43, 44, 47],
  [48, 49, 50, 53, 58, 144, 145, 146, 149, 154, 181, 186],
  [68, 70, 71, 72, 73, 75, 76, 79],
  [132, 134, 135, 136, 137, 139, 140, 143],
  [160, 161, 162, 163],
  [260, 262, 263, 264, 265, 267, 268, 271],
  [0, 1, 2, 5, 10, 260, 261, 264, 266, 268],
  [20, 22, 24, 25, 28, 272, 273, 274, 278, 281],
  [36, 38, 40, 41, 44, 288, 289, 290, 294, 297],
  [132, 134, 136, 137, 140, 384, 385, 386, 390, 393],
  [0, 1, 2, 5, 10, 36, 37, 40, 42, 44],
  [68, 70, 72, 73, 76, 96, 97, 98, 102, 105],
  [132, 134, 136, 137, 140, 160, 161, 162, 166, 169],
  [260, 262, 264, 265, 268, 288, 289, 290, 294, 297],
  [0, 1, 2, 5, 10, 20, 21, 24, 26, 28],
  [132, 134, 136, 137, 140, 144, 145, 146, 150, 153],
  [260, 262, 264, 265, 268, 272, 273, 274, 278, 281]
]

theorem recordedCycles_checked : recordedCycles.all cycleCheck = true := by decide

theorem recordedCycles_excluded {m : Nat} (p : Snake m) :
    ∀ c ∈ recordedCycles, ¬ (∀ v ∈ c, InPath p v) := by
  intro c hc hs
  have h := cycleCheck_sound c (List.all_eq_true.mp recordedCycles_checked c hc)
  have hne : c.toFinset.Nonempty := by
    cases c with
    | nil => exact False.elim (h.1 rfl)
    | cons a tail => exact ⟨a, by simp⟩
  apply two_neighbor_set_not_selected p c.toFinset hne
  · intro v hv
    obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := h.2 v (List.mem_toFinset.mp hv)
    exact ⟨a, List.mem_toFinset.mpr ha, b, List.mem_toFinset.mpr hb, hab, hva, hvb⟩
  · intro v hv
    exact hs v (List.mem_toFinset.mp hv)

#print axioms recordedCycles_excluded
#print axioms subset_has_low_degree
#print axioms two_neighbor_set_not_selected
end Snake9.CycleExclusion
