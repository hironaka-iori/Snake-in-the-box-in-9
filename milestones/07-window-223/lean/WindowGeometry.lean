import BallClauseLogic
import Mathlib.Tactic

namespace Snake9.WindowGeometry
open BallClauseLogic Classical
noncomputable section
set_option maxHeartbeats 1000000

/-- Every selected vertex of a nontrivial snake has a selected neighbor. -/
theorem selected_has_neighbor {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    {v : Vertex} (hv : InPath p v) : ∃ w, InPath p w ∧ Adj v w := by
  obtain ⟨i,rfl⟩ := hv
  by_cases hi : i.val = 0
  · let j : Fin (m+1) := ⟨1,by omega⟩
    exact ⟨p.vertex j,⟨j,rfl⟩,(path_adj_iff p i j).mpr (Or.inl (by simp [j,hi]))⟩
  · let j : Fin (m+1) := ⟨i.val-1,by omega⟩
    refine ⟨p.vertex j,⟨j,rfl⟩,(path_adj_iff p i j).mpr (Or.inr ?_)⟩
    dsimp [j]
    omega

/-- A full-neighborhood list gives the positive-degree clause in the window CNF. -/
theorem positive_degree_clause {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (v : Vertex) (neighbors : List Vertex)
    (hcover : ∀ w, Adj v w → w ∈ neighbors) :
    ¬ InPath p v ∨ ∃ w ∈ neighbors, InPath p w := by
  classical
  by_cases hv : InPath p v
  · obtain ⟨w,hw,ha⟩ := selected_has_neighbor p hm hv
    exact Or.inr ⟨w,hcover w ha,hw⟩
  · exact Or.inl hv

/-- Filtering any duplicate-free list by the actual endpoint predicate yields at most two vertices. -/
theorem endpoint_list_budget {m : Nat} (p : Snake m) (xs : List Vertex)
    (hn : xs.Nodup) : (xs.filter (fun v => decide (Endpoint p v))).length ≤ 2 := by
  classical
  let ys := xs.filter (fun v => decide (Endpoint p v))
  have hy : ys.Nodup := hn.filter _
  have hs : ys.toFinset ⊆ {p.vertex 0,p.vertex (Fin.last m)} := by
    intro v hv
    have he : Endpoint p v := of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hv)).2
    obtain ⟨i,rfl⟩ := he.1
    rcases low_degree_index_is_endpoint p i he.2 with h | h
    · have hi : i=0 := Fin.ext h
      simp [hi]
    · have hi : i=Fin.last m := Fin.ext h
      simp [hi]
  have hc := (Finset.card_le_card hs).trans Finset.card_le_two
  rw [List.toFinset_card_of_nodup hy] at hc
  exact hc

noncomputable def endpointCount {m : Nat} (p : Snake m) (xs : List Vertex) : Nat :=
  xs.countP (fun v => decide (Endpoint p v))

theorem endpointCount_le_two {m : Nat} (p : Snake m) (xs : List Vertex)
    (hn : xs.Nodup) : endpointCount p xs ≤ 2 := by
  classical
  simpa [endpointCount,List.countP_eq_length_filter] using endpoint_list_budget p xs hn

theorem endpointCount_append {m : Nat} (p : Snake m) (xs : List Vertex) (v : Vertex) :
    endpointCount p (xs ++ [v]) = endpointCount p xs + if Endpoint p v then 1 else 0 := by
  classical
  simp [endpointCount,List.countP_append]

/-- The five sequential at-most-two clauses, interpreted by exact prefix counts. -/
def CounterClauses (n : Nat) (e : Bool) : Prop :=
  let next := n + if e then 1 else 0
  (e = false ∨ 1 ≤ next) ∧
  (¬ 1 ≤ n ∨ 1 ≤ next) ∧
  (¬ 2 ≤ n ∨ 2 ≤ next) ∧
  (e = false ∨ ¬ 1 ≤ n ∨ 2 ≤ next) ∧
  (e = false ∨ ¬ 2 ≤ n)

theorem counter_clauses_of_budget (n : Nat) (e : Bool)
    (h : n + (if e then 1 else 0) ≤ 2) : CounterClauses n e := by
  cases e <;> simp_all [CounterClauses] <;> omega

/-- This discharges the endpoint-counter schema using an actual snake, for every
ordered duplicate-free prefix of the encoded interior vertex list. -/
theorem endpoint_counter_clauses {m : Nat} (p : Snake m) (xs : List Vertex) (v : Vertex)
    (hn : (xs ++ [v]).Nodup) :
    CounterClauses (endpointCount p xs) (decide (Endpoint p v)) := by
  classical
  apply counter_clauses_of_budget
  have h := endpointCount_le_two p (xs ++ [v]) hn
  simpa [endpointCount_append] using h

#print axioms selected_has_neighbor
#print axioms positive_degree_clause
#print axioms endpoint_list_budget
#print axioms endpoint_counter_clauses
end
end Snake9.WindowGeometry
