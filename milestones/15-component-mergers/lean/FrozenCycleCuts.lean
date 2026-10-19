import CycleCuts

namespace Snake9.ComponentMergers
open Finset Classical

/-- The signed solver bound is exactly the strict cycle-cardinality cut.
    Integer subtraction is essential when the frozen vertices already contain C. -/
theorem frozen_cut_iff (c frozen changing : Finset Vertex)
    (h : Disjoint frozen changing) :
    ((c ∩ changing).card : Int) ≤ (c.card : Int) - 1 - ((c ∩ frozen).card : Int) ↔
      (c ∩ (frozen ∪ changing)).card < c.card := by
  have hd : Disjoint (c ∩ frozen) (c ∩ changing) :=
    h.mono (Finset.inter_subset_right) (Finset.inter_subset_right)
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hd]
  omega

theorem frozen_complete_cycle_impossible (c frozen changing : Finset Vertex)
    (hc : c ⊆ frozen) :
    ¬ (((c ∩ changing).card : Int) ≤ (c.card : Int) - 1 - ((c ∩ frozen).card : Int)) := by
  have he : c ∩ frozen = c := Finset.inter_eq_left.mpr hc
  rw [he]
  omega

#print axioms frozen_cut_iff
#print axioms frozen_complete_cycle_impossible
end Snake9.ComponentMergers
