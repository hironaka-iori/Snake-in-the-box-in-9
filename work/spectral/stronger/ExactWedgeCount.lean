import SquareIncidence

/- This extension sharpens the already proved wedge upper bound to an equality.
   It retains Snake9.Snake and all existing incidence definitions. -/
namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 200000

theorem internal_has_wedge {m : Nat} (p : Snake m) (v : Vertex)
    (hv : v ∈ internalSet p) : ∃ ab : AxisPair, wedge p ab v = 1 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  have hi0 : 0 < i.val := (Finset.mem_Ioo.mp hi).1
  have him : i.val < m := (Finset.mem_Ioo.mp hi).2
  let j : Fin (m+1) := ⟨i.val-1, by omega⟩
  let k : Fin (m+1) := ⟨i.val+1, by omega⟩
  have haj : Adj (p.vertex i) (p.vertex j) :=
    (path_adj_iff p i j).mpr (Or.inr (by dsimp [j]; omega))
  have hak : Adj (p.vertex i) (p.vertex k) :=
    (path_adj_iff p i k).mpr (Or.inl rfl)
  obtain ⟨a, ha, hea⟩ := (adj_iff_coordinate_flip _ _).mp haj
  obtain ⟨b, hb, heb⟩ := (adj_iff_coordinate_flip _ _).mp hak
  let ca : Coord := ⟨a, ha⟩
  let cb : Coord := ⟨b, hb⟩
  have hleft : flip ca (p.vertex i) = p.vertex j := Fin.ext hea.symm
  have hright : flip cb (p.vertex i) = p.vertex k := Fin.ext heb.symm
  have hne : a ≠ b := by
    intro he
    have hvertices : p.vertex j = p.vertex k := by
      apply Fin.ext
      exact hea.trans (he ▸ heb.symm)
    have hv := congrArg Fin.val (p.distinct j k hvertices)
    dsimp [j,k] at hv
    omega
  by_cases hab : a < b
  · let ab : AxisPair := ⟨(ca,cb),hab⟩
    refine ⟨ab, ?_⟩
    apply if_pos
    exact ⟨⟨i,rfl⟩, ⟨j,hleft.symm⟩, ⟨k,hright.symm⟩⟩
  · let ab : AxisPair := ⟨(cb,ca),by dsimp [ca,cb]; omega⟩
    refine ⟨ab, ?_⟩
    apply if_pos
    exact ⟨⟨i,rfl⟩, ⟨k,hright.symm⟩, ⟨j,hleft.symm⟩⟩

theorem wedge_at_vertex_eq {m : Nat} (p : Snake m) (v : Vertex) :
    (∑ ab : AxisPair, wedge p ab v) = if v ∈ internalSet p then 1 else 0 := by
  apply Nat.le_antisymm (wedge_at_vertex_le p v)
  by_cases hv : v ∈ internalSet p
  · rw [if_pos hv]
    obtain ⟨ab, hab⟩ := internal_has_wedge p v hv
    calc
      1 = wedge p ab v := hab.symm
      _ ≤ ∑ cd : AxisPair, wedge p cd v :=
        Finset.single_le_sum (fun cd _ => Nat.zero_le (wedge p cd v)) (Finset.mem_univ ab)
  · rw [if_neg hv]
    exact Nat.zero_le _

theorem wedge_total_exact {m : Nat} (p : Snake m) : totalWedge p = m-1 := by
  calc
    totalWedge p = ∑ v : Vertex, ∑ ab : AxisPair, wedge p ab v := by
      unfold totalWedge
      rw [Finset.sum_comm]
    _ = ∑ v : Vertex, if v ∈ internalSet p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact wedge_at_vertex_eq p v
    _ = (internalSet p).card := by simp
    _ = m-1 := internal_count p

theorem exact_defect_identity {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    2 * totalEmptyAnchored p + 4 * totalSingleton p + 140 * (m+1) + 8 = 36864 := by
  have h := global_identity p
  rw [selected_total p, wedge_total_exact p] at h
  omega

#print axioms internal_has_wedge
#print axioms wedge_total_exact
#print axioms exact_defect_identity
end
end Snake9.SquareIncidence

