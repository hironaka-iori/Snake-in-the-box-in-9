import CriticalCase173

open scoped BigOperators
namespace Snake9.SmallLoss174
open Count171 Critical173
noncomputable section

-- This counts vertices with nonzero remainder, not vertices with empty squares.
def positiveLossCorners {m : Nat} (p : Snake m) : Finset Vertex := by
  classical
  exact Finset.univ.filter (fun q => 0 < cornerLoss p q)

theorem positive_corner_count_le_loss {m : Nat} (p : Snake m) :
    (positiveLossCorners p).card ≤ totalLoss p := by
  classical
  calc
    (positiveLossCorners p).card = ∑ q ∈ positiveLossCorners p, 1 := by simp
    _ ≤ ∑ q ∈ positiveLossCorners p, cornerLoss p q := by
      apply Finset.sum_le_sum
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    _ ≤ totalLoss p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)

theorem small_loss_sparse {m : Nat} (p : Snake m) (hl : totalLoss p ≤ 3) :
    (positiveLossCorners p).card ≤ 3 := by
  have hc := positive_corner_count_le_loss p
  omega

theorem zero_corner_divisibility {m : Nat} (p : Snake m) (q : Vertex)
    (hz : cornerLoss p q = 0) : selectedNeighborCount p q ∣ 12 * emptySquareCount p q := by
  unfold cornerLoss at hz
  split at hz
  · rename_i hd
    rw [hd]
    exact zero_dvd_iff.mpr hz
  · exact Nat.dvd_of_mod_eq_zero hz

theorem small_loss_degree_five_restriction {m : Nat} (p : Snake m) (q : Vertex)
    (hl : totalLoss p ≤ 3) (hd : selectedNeighborCount p q = 5) :
    emptySquareCount p q % 5 ≠ 2 := by
  have hc := corner_loss_le_total p q
  have hr : cornerLoss p q = (12 * emptySquareCount p q) % 5 := by
    simp [cornerLoss,hd]
  rw [hr] at hc
  intro he
  have hmod : (12 * emptySquareCount p q) % 5 = 4 := by
    rw [Nat.mul_mod,he]
  omega

theorem outside_positive_support_divisible {m : Nat} (p : Snake m) (q : Vertex)
    (hq : q ∉ positiveLossCorners p) :
    selectedNeighborCount p q ∣ 12 * emptySquareCount p q := by
  classical
  have hz : cornerLoss p q = 0 := by
    have hn : ¬ 0 < cornerLoss p q := by
      intro hp
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
    omega
  exact zero_corner_divisibility p q hz

#print axioms positive_corner_count_le_loss
#print axioms small_loss_sparse
#print axioms zero_corner_divisibility
#print axioms small_loss_degree_five_restriction
#print axioms outside_positive_support_divisible
end Snake9.SmallLoss174
