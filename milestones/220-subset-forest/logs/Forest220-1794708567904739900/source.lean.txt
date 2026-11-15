import LayerJoining
import Capacity209

set_option Elab.async false

namespace Forest220
open LayerJoining

/-- Ambient edges within selected positions of an actual induced path have
at least one fewer edge than vertices when a selected position is supplied. -/
theorem selected_edges_add_one_le {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m)
    (selected : List (Fin (m + 1)))
    (edges : List (Fin (m + 1) × Fin (m + 1)))
    (distinct_edges : edges.Nodup)
    (valid : ∀ e, e ∈ edges → e.1 ∈ selected ∧ e.2 ∈ selected ∧
      e.1.val < e.2.val ∧ R (p.vertex e.1) (p.vertex e.2))
    (anchor : Fin (m + 1)) (chosen : anchor ∈ selected) :
    edges.length + 1 ≤ selected.length := by
  have consecutive : ∀ e, e ∈ edges → e.1.val + 1 = e.2.val := by
    intro e he
    have h := valid e he
    exact (p.induced e.1 e.2 h.2.2.1).mp h.2.2.2
  let charge : Fin (m + 1) × Fin (m + 1) → Nat := fun e =>
    if e.1.val < anchor.val then e.1.val else e.2.val
  have avoids : ∀ e, e ∈ edges → charge e ≠ anchor.val := by
    intro e he
    have hstep := consecutive e he
    by_cases h : e.1.val < anchor.val <;>
      simp only [charge, h, if_true, if_false] <;> omega
  have injective_on : ∀ a, a ∈ edges → ∀ b, b ∈ edges →
      charge a = charge b → a = b := by
    intro a ha b hb equal
    have astep := consecutive a ha
    have bstep := consecutive b hb
    have first : a.1.val = b.1.val := by
      by_cases left : a.1.val < anchor.val <;>
        by_cases right : b.1.val < anchor.val <;>
        simp only [charge, left, right, if_true, if_false] at equal <;> omega
    have second : a.2.val = b.2.val := by omega
    exact Prod.ext (Fin.ext first) (Fin.ext second)
  have charged_distinct : (edges.map charge).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ distinct_edges
    intro a b ha hb unequal equal
    exact unequal (injective_on a ha b hb equal)
  have with_anchor : (anchor.val :: edges.map charge).Nodup := by
    simp only [List.nodup_cons]
    constructor
    · intro h
      obtain ⟨e, he, equal⟩ := List.mem_map.mp h
      exact avoids e he equal
    · exact charged_distinct
  have included : ∀ k, k ∈ anchor.val :: edges.map charge →
      k ∈ selected.map Fin.val := by
    intro k hk
    rcases List.mem_cons.mp hk with equal | hm
    · subst k
      exact List.mem_map.mpr ⟨anchor, chosen, rfl⟩
    · obtain ⟨e, he, equal⟩ := List.mem_map.mp hm
      have endpoints := valid e he
      rw [← equal]
      by_cases h : e.1.val < anchor.val
      · simp only [charge, h, if_true]
        exact List.mem_map.mpr ⟨e.1, endpoints.1, rfl⟩
      · simp only [charge, h, if_false]
        exact List.mem_map.mpr ⟨e.2, endpoints.2.1, rfl⟩
  have bound := Capacity209.distinct_length_le (anchor.val :: edges.map charge)
    (selected.map Fin.val) with_anchor included
  simpa only [List.length_cons, List.length_map] using bound

/-- The empty-subset case is included without assuming a selected anchor. -/
theorem selected_edges_le {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m)
    (selected : List (Fin (m + 1)))
    (edges : List (Fin (m + 1) × Fin (m + 1)))
    (distinct_edges : edges.Nodup)
    (valid : ∀ e, e ∈ edges → e.1 ∈ selected ∧ e.2 ∈ selected ∧
      e.1.val < e.2.val ∧ R (p.vertex e.1) (p.vertex e.2)) :
    edges.length ≤ selected.length := by
  cases selected with
  | nil =>
      cases edges with
      | nil => simp
      | cons e tail =>
          have impossible := (valid e (by simp)).1
          exact False.elim (List.not_mem_nil impossible)
  | cons anchor tail =>
      have bound := selected_edges_add_one_le p (anchor :: tail) edges
        distinct_edges valid anchor (by simp)
      omega

/-- The uniform forest inequality includes an optional selected marked
vertex. Its membership is supplied from the actual path selection. -/
theorem subset_forest_bound {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m)
    (selected : List (Fin (m + 1)))
    (edges : List (Fin (m + 1) × Fin (m + 1)))
    (distinct_edges : edges.Nodup)
    (valid : ∀ e, e ∈ edges → e.1 ∈ selected ∧ e.2 ∈ selected ∧
      e.1.val < e.2.val ∧ R (p.vertex e.1) (p.vertex e.2))
    (marked : Bool)
    (marked_selected : marked = true → ∃ i, i ∈ selected) :
    edges.length + (if marked then 1 else 0) ≤ selected.length := by
  cases marked with
  | false => simpa using selected_edges_le p selected edges distinct_edges valid
  | true =>
      obtain ⟨anchor, ha⟩ := marked_selected rfl
      simpa using selected_edges_add_one_le p selected edges distinct_edges valid anchor ha

/-- Signed degree-sum accounting gives the boundary-plus-endpoint form. -/
theorem degree_boundary_iff (X E Y B marked : Int)
    (degree_sum : 2 * X - E = 2 * Y + B) :
    (Y ≤ X - marked) ↔ 2 * marked ≤ B + E := by
  omega

#print axioms selected_edges_add_one_le
#print axioms selected_edges_le
#print axioms subset_forest_bound
#print axioms degree_boundary_iff
end Forest220
