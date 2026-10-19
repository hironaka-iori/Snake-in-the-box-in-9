import CycleCuts
namespace Snake9.CycleReservoirs
open Finset Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def a : List Vertex := [0,1,17,25,27,31,15,13,12,28,20,22,18,2]
def b : List Vertex := [3,11,9,8,24,26,30,14,6,4,5,21,23,19]
theorem base_sizes : a.length = 14 ∧ b.length = 14 := by decide
theorem bases_distinct : a.Nodup ∧ b.Nodup := by decide
theorem bases_disjoint : Disjoint a.toFinset b.toFinset := by decide
theorem a_induced_cycle : ∀ i j : Fin 14,
    Adj a[i.val]! a[j.val]! ↔ (i.val+1)%14 = j.val ∨ (j.val+1)%14 = i.val := by decide
theorem b_induced_cycle : ∀ i j : Fin 14,
    Adj b[i.val]! b[j.val]! ↔ (i.val+1)%14 = j.val ∨ (j.val+1)%14 = i.val := by decide

/-- Opposite colors cannot select the same base vertex from disjoint sets. -/
theorem opposite_colors_disjoint {V : Type} [DecidableEq V] (a b : Finset V)
    (hd : Disjoint a b) (s t : Bool) (hne : s ≠ t) (v : V)
    (hs : v ∈ if s then a else b) (ht : v ∈ if t then a else b) : False := by
  cases s <;> cases t
  · exact hne rfl
  · exact Finset.disjoint_left.mp hd ht hs
  · exact Finset.disjoint_left.mp hd hs ht
  · exact hne rfl

/-- Keeping whole 14-cycles and one nontrivial proper path from a 14-cycle
    cannot give 197 vertices. New connections or replacements are needed. -/
theorem no_simple_197_trim (k r : Nat) (hr : 2 ≤ r) (hr' : r ≤ 13) :
    14*k+r ≠ 197 := by omega

theorem connector_degrees :
    (a.filter (fun v => decide (Adj 7 v))).length = 1 ∧
    (b.filter (fun v => decide (Adj 7 v))).length = 4 ∧
    (a.filter (fun v => decide (Adj 10 v))).length = 1 ∧
    (b.filter (fun v => decide (Adj 10 v))).length = 4 ∧
    (a.filter (fun v => decide (Adj 16 v))).length = 4 ∧
    (b.filter (fun v => decide (Adj 16 v))).length = 1 ∧
    (a.filter (fun v => decide (Adj 29 v))).length = 4 ∧
    (b.filter (fun v => decide (Adj 29 v))).length = 1 := by decide

/-- A selected connector using an external edge can retain at most one of
    four internal neighbors. The local replacement cost is at least three. -/
theorem four_neighbor_connector_cost {m : Nat} (p : Snake m)
    (v z : Vertex) (neighbors : Finset Vertex)
    (hfour : neighbors.card = 4) (hv : InPath p v) (hz : InPath p z)
    (hvz : Adj v z) (hzout : z ∉ neighbors)
    (hadj : ∀ w ∈ neighbors, Adj v w) :
    3 ≤ (neighbors.filter (fun w => ¬ InPath p w)).card := by
  classical
  have hone : (neighbors.filter (fun w => InPath p w)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haN,haP⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbN,hbP⟩ := Finset.mem_filter.mp hb
    rcases selected_three_neighbors_repeat p hv haP hbP hz (hadj a haN) (hadj b hbN) hvz with hab | haz | hbz
    · exact hab
    · exact False.elim (hzout (haz ▸ haN))
    · exact False.elim (hzout (hbz ▸ hbN))
  have hsum := Finset.filter_card_add_filter_neg_card_eq_card (s := neighbors) (fun w => InPath p w)
  omega

#print axioms base_sizes
#print axioms bases_distinct
#print axioms bases_disjoint
#print axioms a_induced_cycle
#print axioms b_induced_cycle
#print axioms opposite_colors_disjoint
#print axioms no_simple_197_trim
#print axioms connector_degrees
#print axioms four_neighbor_connector_cost
end Snake9.CycleReservoirs
