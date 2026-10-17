import Regrowth96Bridge

namespace Snake9.Regrowth96
noncomputable section
local instance parityDec (P : Prop) : Decidable P := Classical.propDecidable P
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem parity_count (p : Snake 97) (b : Bool) :
    ((List.ofFn p.vertex).filter (fun v => bitParity v.val == b)).length = 49 := by
  rw [← List.countP_eq_length_filter]
  have he : (List.ofFn p.vertex).map (fun v => bitParity v.val == b) =
      List.ofFn (fun i : Fin 98 => (bitParity (p.vertex 0).val ^^ (i.val % 2 == 1)) == b) := by
    rw [map_ofFn]
    congr 1
    funext i
    rw [parity_along p i.val (by omega)]
    rfl
  have hc : (List.ofFn p.vertex).countP (fun v => bitParity v.val == b) =
      ((List.ofFn p.vertex).map (fun v => bitParity v.val == b)).countP id := by
    rw [List.countP_map]
    rfl
  rw [hc,he]
  cases b <;> cases bitParity (p.vertex 0).val <;> decide

theorem selected_side_bound (p : Snake 97) (b : Bool) (side : List Vertex)
    (hn : side.Nodup) (hside : ∀ v ∈ side, bitParity v.val = b) :
    (side.filter (fun v => decide (InPath p v))).length ≤ 49 := by
  have hb := nodup_subset_length
    (side.filter (fun v => decide (InPath p v)))
    ((List.ofFn p.vertex).filter (fun v => bitParity v.val == b))
    (hn.sublist List.filter_sublist) (by
      intro v hv
      obtain ⟨hm,hs⟩ := List.mem_filter.mp hv
      have hs : InPath p v := of_decide_eq_true hs
      exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr hs, by simp only [hside v hm, beq_self_eq_true]⟩)
  rw [parity_count] at hb
  exact hb

theorem absent_side_bound (p : Snake 97) (b : Bool) (side : List Vertex)
    (hcover : ∀ v, InPath p v → bitParity v.val = b → v ∈ side) :
    (side.filter (fun v => !(decide (InPath p v)))).length ≤ side.length - 49 := by
  have hn := (path_nodup p).sublist (List.filter_sublist (p := fun v => bitParity v.val == b))
  have hc : ((List.ofFn p.vertex).filter (fun v => bitParity v.val == b)) ⊆
      side.filter (fun v => decide (InPath p v)) := by
    intro v hv
    obtain ⟨hv,hpar⟩ := List.mem_filter.mp hv
    have hp : InPath p v := List.mem_ofFn.mp hv
    exact List.mem_filter.mpr ⟨hcover v hp (beq_iff_eq.mp hpar),by simp [hp]⟩
  have hb := nodup_subset_length _ _ hn hc
  rw [parity_count] at hb
  have he := filter_partition side (fun v => decide (InPath p v))
  omega

#print axioms selected_side_bound
#print axioms absent_side_bound
end
end Snake9.Regrowth96
