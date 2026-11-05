import EmptyEight171
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
namespace Snake9.Count171

noncomputable def selectedNeighborCount {m : Nat} (p : Snake m) (q : Vertex) : Nat := by
  classical
  exact (Finset.univ.filter (fun a : Coord => InPath p (vxor q (unit a)))).card

noncomputable def cornerLoss {m : Nat} (p : Snake m) (q : Vertex) : Nat :=
  if selectedNeighborCount p q = 0 then 12 * emptySquareCount p q
  else (12 * emptySquareCount p q) % selectedNeighborCount p q

noncomputable def totalLoss {m : Nat} (p : Snake m) : Nat :=
  ∑ q : Vertex, cornerLoss p q

theorem undominated_neighbor_count_zero {m : Nat} (p : Snake m) (q : Vertex)
    (hq : ∀ v, InPath p v → ¬ Adj q v) : selectedNeighborCount p q = 0 := by
  classical
  unfold selectedNeighborCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro a _ hs
  exact Component170.translated_units_absent p q hq a
    ((Component170.in_translate_iff p q (unit a)).mpr hs)

theorem corner_loss_le_total {m : Nat} (p : Snake m) (q : Vertex) :
    cornerLoss p q ≤ totalLoss p := by
  classical
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

theorem undominated_total_loss_ge_96 {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q : Vertex) (hq : ∀ v, InPath p v → ¬ Adj q v) : 96 ≤ totalLoss p := by
  have he := undominated_eight_empty_squares p hm q hq
  have hd := undominated_neighbor_count_zero p q hq
  have hc : 96 ≤ cornerLoss p q := by
    rw [cornerLoss, if_pos hd]
    omega
  exact hc.trans (corner_loss_le_total p q)

theorem small_loss_dominates {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (hl : totalLoss p ≤ 95) : ∀ q : Vertex, ∃ v, InPath p v ∧ Adj q v := by
  classical
  intro q
  by_contra hn
  have hq : ∀ v, InPath p v → ¬ Adj q v := by
    intro v hv ha
    exact hn ⟨v,hv,ha⟩
  have hlow := undominated_total_loss_ge_96 p hm q hq
  omega

#print axioms undominated_neighbor_count_zero
#print axioms corner_loss_le_total
#print axioms undominated_total_loss_ge_96
#print axioms small_loss_dominates
end Snake9.Count171
