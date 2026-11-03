import Mathlib.Tactic

namespace Snake9.MissingDegree135

open scoped BigOperators

theorem nonincident_card_eq_sub_degree {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (u : α) :
    (F.filter (fun e => u ∉ e)).card =
      F.card - (F.filter (fun e => u ∈ e)).card := by
  have hfilter : F.filter (fun e => u ∉ e) =
      F \ (F.filter (fun e => u ∈ e)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hfilter, Finset.card_sdiff (Finset.filter_subset _ _)]

theorem sum_degrees_eq_sum_intersections {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Finset (Finset α)) :
    (∑ u ∈ A, (F.filter (fun e => u ∈ e)).card) =
      ∑ e ∈ F, (A.filter (fun u => u ∈ e)).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem card_le_sum_degrees {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Finset (Finset α))
    (hmeet : ∀ e ∈ F, (e ∩ A).Nonempty) :
    F.card ≤ ∑ u ∈ A, (F.filter (fun e => u ∈ e)).card := by
  rw [sum_degrees_eq_sum_intersections A F]
  calc
    F.card = ∑ _e ∈ F, 1 := by simp
    _ ≤ ∑ e ∈ F, (A.filter (fun u => u ∈ e)).card := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨u,hu⟩ := hmeet e he
      have hnonempty : (A.filter (fun u => u ∈ e)).Nonempty :=
        ⟨u,Finset.mem_filter.mpr
          ⟨(Finset.mem_inter.mp hu).2,(Finset.mem_inter.mp hu).1⟩⟩
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr hnonempty)

theorem crossing_intersection_card_eq_one {α : Type*} [DecidableEq α]
    (A e : Finset α) (hsize : e.card = 2)
    (hmeet : (e ∩ A).Nonempty) (hcross : ¬ e ⊆ A) :
    (e ∩ A).card = 1 := by
  have hpos : 0 < (e ∩ A).card := Finset.card_pos.mpr hmeet
  have hle : (e ∩ A).card ≤ e.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hlt : (e ∩ A).card < 2 := by
    by_contra hn
    have heq : e ∩ A = e :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    apply hcross
    intro u hu
    have hu' : u ∈ e ∩ A := by
      rw [heq]
      exact hu
    exact (Finset.mem_inter.mp hu').2
  omega

theorem sum_degree_add_crossing_degree {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Finset (Finset α))
    (hsize : ∀ e ∈ F, e.card = 2)
    (hmeet : ∀ e ∈ F, (e ∩ A).Nonempty) :
    (∑ u ∈ A, ((F.filter (fun e => u ∈ e)).card +
      (F.filter (fun e => u ∈ e ∧ ¬ e ⊆ A)).card)) = 2 * F.card := by
  have hcrosssum :
      (∑ u ∈ A, (F.filter (fun e => u ∈ e ∧ ¬ e ⊆ A)).card) =
        ∑ e ∈ F, (A.filter (fun u => u ∈ e ∧ ¬ e ⊆ A)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hedge : ∀ e ∈ F,
      (A.filter (fun u => u ∈ e)).card +
        (A.filter (fun u => u ∈ e ∧ ¬ e ⊆ A)).card = 2 := by
    intro e he
    have hfilter : A.filter (fun u => u ∈ e) = e ∩ A := by
      ext u
      simp [and_comm]
    by_cases hsub : e ⊆ A
    · have hinter : e ∩ A = e := Finset.inter_eq_left.mpr hsub
      simp [hsub, hfilter, hinter, hsize e he]
    · have hone : (e ∩ A).card = 1 :=
        crossing_intersection_card_eq_one A e (hsize e he) (hmeet e he) hsub
      simp [hsub, hfilter, hone]
  calc
    (∑ u ∈ A, ((F.filter (fun e => u ∈ e)).card +
      (F.filter (fun e => u ∈ e ∧ ¬ e ⊆ A)).card)) =
        (∑ u ∈ A, (F.filter (fun e => u ∈ e)).card) +
          (∑ u ∈ A, (F.filter (fun e => u ∈ e ∧ ¬ e ⊆ A)).card) :=
      Finset.sum_add_distrib
    _ = (∑ e ∈ F, (A.filter (fun u => u ∈ e)).card) +
        (∑ e ∈ F, (A.filter (fun u => u ∈ e ∧ ¬ e ⊆ A)).card) := by
      rw [sum_degrees_eq_sum_intersections A F, hcrosssum]
    _ = ∑ e ∈ F, ((A.filter (fun u => u ∈ e)).card +
        (A.filter (fun u => u ∈ e ∧ ¬ e ⊆ A)).card) :=
      Finset.sum_add_distrib.symm
    _ = ∑ _e ∈ F, 2 := Finset.sum_congr rfl hedge
    _ = 2 * F.card := by simp [Nat.mul_comm]

theorem at_most_one_vertex_with_three_crossings
    {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Finset (Finset α))
    (hsize : ∀ e ∈ F, e.card = 2) (hcard : F.card = 3) :
    (A.filter (fun u =>
      (F.filter (fun e => u ∈ e ∧ ¬ e ⊆ A)).card = 3)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huA,huCard⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvA,hvCard⟩ := Finset.mem_filter.mp hv
  have huAll : ∀ e ∈ F, u ∈ e ∧ ¬ e ⊆ A :=
    Finset.card_filter_eq_iff.mp (huCard.trans hcard.symm)
  have hvAll : ∀ e ∈ F, v ∈ e ∧ ¬ e ⊆ A :=
    Finset.card_filter_eq_iff.mp (hvCard.trans hcard.symm)
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
  have hue := huAll e he
  have hve := hvAll e he
  have hmeet : (e ∩ A).Nonempty :=
    ⟨u,Finset.mem_inter.mpr ⟨hue.1,huA⟩⟩
  have hone : (e ∩ A).card = 1 :=
    crossing_intersection_card_eq_one A e (hsize e he) hmeet hue.2
  exact Finset.card_le_one.mp (show (e ∩ A).card ≤ 1 by omega)
    u (Finset.mem_inter.mpr ⟨hue.1,huA⟩)
    v (Finset.mem_inter.mpr ⟨hve.1,hvA⟩)

#print axioms nonincident_card_eq_sub_degree
#print axioms sum_degrees_eq_sum_intersections
#print axioms card_le_sum_degrees
#print axioms crossing_intersection_card_eq_one
#print axioms sum_degree_add_crossing_degree
#print axioms at_most_one_vertex_with_three_crossings

end Snake9.MissingDegree135
