import Residual226
import Capacity209

set_option Elab.async false

namespace ResidualCapacity226
open LayerJoining

/-- Distinct positions of an actual path require as many available vertices.
The containing pool may be the residual component or one of its colours. -/
theorem selected_capacity {R : Nat → Nat → Prop} {n : Nat}
    (p : InducedPath Nat R n) (selected : List (Fin (n + 1))) (pool : List Nat)
    (distinct : selected.Nodup)
    (fit : ∀ i, i ∈ selected → p.vertex i ∈ pool) :
    selected.length ≤ pool.length := by
  have mapped_distinct : (selected.map p.vertex).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ distinct
    intro i j hi hj unequal equal
    exact unequal (p.distinct i j equal)
  have subset : ∀ v, v ∈ selected.map p.vertex → v ∈ pool := by
    intro v hv
    obtain ⟨i, hi, equal⟩ := List.mem_map.mp hv
    rw [← equal]
    exact fit i hi
  have bound := Capacity209.distinct_length_le (selected.map p.vertex) pool
    mapped_distinct subset
  simpa only [List.length_map] using bound

theorem full_capacity {R : Nat → Nat → Prop} {n : Nat}
    (p : InducedPath Nat R n) (positions : List (Fin (n + 1))) (pool : List Nat)
    (distinct : positions.Nodup) (count : positions.length = n + 1)
    (fit : ∀ i, p.vertex i ∈ pool) : n + 1 ≤ pool.length := by
  have bound := selected_capacity p positions pool distinct (fun i _ => fit i)
  simpa only [count] using bound

/-- Each selected colour class must fit into that colour of the residual
component. Alternation determines which indices belong to the class. -/
theorem colour_capacity {R : Nat → Nat → Prop} {n : Nat}
    (p : InducedPath Nat R n) (selected : List (Fin (n + 1))) (pool : List Nat)
    (colour : Nat → Bool) (shade : Bool) (distinct : selected.Nodup)
    (fit : ∀ i, i ∈ selected → p.vertex i ∈ pool)
    (selected_colour : ∀ i, i ∈ selected → colour (p.vertex i) = shade) :
    selected.length ≤ (pool.filter (fun v => colour v == shade)).length := by
  apply selected_capacity p selected _ distinct
  intro i hi
  apply List.mem_filter.mpr
  exact ⟨fit i hi, by simp [selected_colour i hi]⟩

#print axioms selected_capacity
#print axioms full_capacity
#print axioms colour_capacity
end ResidualCapacity226
