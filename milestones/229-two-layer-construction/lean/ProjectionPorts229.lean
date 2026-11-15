import LayerJoining

set_option Elab.async false

namespace ProjectionPorts229
open LayerJoining

/-- Across the two faces, the filtered domain permits only an own-port
coincidence and permits no coincidence with the other upper piece. -/
theorem projection_mask_iff {V : Type} [DecidableEq V]
    (R : V → V → Prop) (domain upper ports other : List V) (x : V) :
    x ∈ domain.filter (fun v =>
      decide ((v ∉ upper ∨ v ∈ ports) ∧ v ∉ other)) ↔
    x ∈ domain ∧
      (∀ y, y ∈ upper → LayerAdj R (x, false) (y, true) → x ∈ ports) ∧
      (∀ y, y ∈ other → ¬ LayerAdj R (x, false) (y, true)) := by
  constructor
  · intro h
    have hm : x ∈ domain ∧ (x ∉ upper ∨ x ∈ ports) ∧ x ∉ other := by
      simpa only [List.mem_filter, decide_eq_true_eq] using h
    refine ⟨hm.1, ?_, ?_⟩
    · intro y hy hedge
      have he : x = y := by simpa [LayerAdj] using hedge
      rcases hm.2.1 with hnot | hport
      · exact False.elim (hnot (he.symm ▸ hy))
      · exact hport
    · intro y hy hedge
      have he : x = y := by simpa [LayerAdj] using hedge
      exact hm.2.2 (he.symm ▸ hy)
  · intro h
    have hown : x ∉ upper ∨ x ∈ ports := by
      by_cases hx : x ∈ upper
      · exact Or.inr (h.2.1 x hx (by simp [LayerAdj]))
      · exact Or.inl hx
    have hother : x ∉ other := by
      intro hx
      exact h.2.2 x hx (by simp [LayerAdj])
    simpa only [List.mem_filter, decide_eq_true_eq] using
      (show x ∈ domain ∧ (x ∉ upper ∨ x ∈ ports) ∧ x ∉ other from
        ⟨h.1, hown, hother⟩)

/-- Given the intended joining equality, the lower-domain restriction is
equivalent to the exact indexed compatibility needed by LayerJoining.join.
The unique exempted projection is the last lower vertex. -/
theorem compatible_iff_projection_filter {V : Type} [DecidableEq V]
    {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b) (domain : List V)
    (hfit : ∀ i, p.vertex i ∈ domain)
    (hjoin : p.vertex ⟨a, by omega⟩ = q.vertex ⟨0, by omega⟩) :
    Compatible p q ↔
    ∀ i, p.vertex i ∈ domain.filter (fun v =>
      decide (v ∉ List.ofFn q.vertex ∨ v = p.vertex ⟨a, by omega⟩)) := by
  constructor
  · intro hc i
    have hown : p.vertex i ∉ List.ofFn q.vertex ∨
        p.vertex i = p.vertex ⟨a, by omega⟩ := by
      by_cases hp : p.vertex i = p.vertex ⟨a, by omega⟩
      · exact Or.inr hp
      · apply Or.inl
        intro hm
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
        have hi : i = (⟨a, by omega⟩ : Fin (a + 1)) :=
          Fin.ext ((hc i j).mp hj.symm).1
        exact hp (congrArg p.vertex hi)
    simpa only [List.mem_filter, decide_eq_true_eq] using And.intro (hfit i) hown
  · intro hmask i j
    constructor
    · intro he
      have hm : p.vertex i ∈ domain ∧
          (p.vertex i ∉ List.ofFn q.vertex ∨
            p.vertex i = p.vertex ⟨a, by omega⟩) := by
        simpa only [List.mem_filter, decide_eq_true_eq] using hmask i
      have hp : p.vertex i = p.vertex ⟨a, by omega⟩ := by
        rcases hm.2 with hnot | hport
        · exact False.elim (hnot (List.mem_ofFn.mpr ⟨j, he.symm⟩))
        · exact hport
      have hi := p.distinct i ⟨a, by omega⟩ hp
      have hj := q.distinct j ⟨0, by omega⟩ (he.symm.trans (hp.trans hjoin))
      exact ⟨congrArg Fin.val hi, congrArg Fin.val hj⟩
    · intro hend
      have hi : i = (⟨a, by omega⟩ : Fin (a + 1)) := Fin.ext hend.1
      have hj : j = (⟨0, by omega⟩ : Fin (b + 1)) := Fin.ext hend.2
      simpa only [hi, hj] using hjoin

/-- A positive-length lower path has a fixed starting anchor distinct from
its joining port. Its upper copy cannot occur anywhere in the upper arm. -/
theorem fixed_lower_anchor_excluded {V : Type} [DecidableEq V]
    {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b) (domain : List V)
    (ha : 0 < a)
    (hmask : ∀ i, p.vertex i ∈ domain.filter (fun v =>
      decide (v ∉ List.ofFn q.vertex ∨ v = p.vertex ⟨a, by omega⟩))) :
    p.vertex ⟨0, by omega⟩ ∉ List.ofFn q.vertex := by
  intro hupper
  have hm : p.vertex ⟨0, by omega⟩ ∈ domain ∧
      (p.vertex ⟨0, by omega⟩ ∉ List.ofFn q.vertex ∨
        p.vertex ⟨0, by omega⟩ = p.vertex ⟨a, by omega⟩) := by
    simpa only [List.mem_filter, decide_eq_true_eq] using hmask ⟨0, by omega⟩
  rcases hm.2 with hnot | he
  · exact hnot hupper
  · have hi := p.distinct ⟨0, by omega⟩ ⟨a, by omega⟩ he
    have hv := congrArg Fin.val hi
    simp only [Fin.val_mk] at hv
    omega

#print axioms projection_mask_iff
#print axioms compatible_iff_projection_filter
#print axioms fixed_lower_anchor_excluded

end ProjectionPorts229
