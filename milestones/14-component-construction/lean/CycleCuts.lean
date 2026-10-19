import CycleExclusion

namespace Snake9.ComponentConstruction
open Finset CycleExclusion Classical

theorem cycle_cut_card {m : Nat} (p : Snake m) (s : Finset Vertex)
    (hne : s.Nonempty)
    (hdegree : ∀ v ∈ s, ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ Adj v a ∧ Adj v b) :
    (s.filter (fun v => InPath p v)).card ≤ s.card - 1 := by
  classical
  have h := two_neighbor_set_not_selected p s hne hdegree
  have hex : ∃ v ∈ s, ¬ InPath p v := by
    by_contra hn
    apply h
    intro v hv
    by_contra hnv
    exact hn ⟨v,hv,hnv⟩
  have hc : (s.filter (fun v => InPath p v)).card < s.card :=
    Finset.card_lt_card (Finset.filter_ssubset.mpr hex)
  exact Nat.le_sub_one_of_lt hc

theorem checked_cycle_cut {m : Nat} (p : Snake m) (c : List Vertex)
    (checked : cycleCheck c = true) :
    (c.toFinset.filter (fun v => InPath p v)).card ≤ c.toFinset.card - 1 := by
  classical
  obtain ⟨hne,hdegree⟩ := cycleCheck_sound c checked
  apply cycle_cut_card p c.toFinset
  · cases c with
    | nil => exact False.elim (hne rfl)
    | cons a tail => exact ⟨a,by simp⟩
  · intro v hv
    obtain ⟨a,ha,b,hb,hab,hva,hvb⟩ := hdegree v (List.mem_toFinset.mp hv)
    exact ⟨a,List.mem_toFinset.mpr ha,b,List.mem_toFinset.mpr hb,hab,hva,hvb⟩

theorem unit_square_checked : cycleCheck [0,1,2,3] = true := by decide

#print axioms cycle_cut_card
#print axioms checked_cycle_cut
#print axioms unit_square_checked
end Snake9.ComponentConstruction
