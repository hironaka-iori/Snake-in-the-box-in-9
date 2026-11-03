import CoordinateRun134
import RunLength134

namespace Snake9.ActualRunBound134
open Snake9.LocalWindow

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The actual coordinate run is bounded by the available coordinates outside
the predicate and the explicitly supplied finite set of missing pairs. -/
theorem length_le_outside_card_or_one_add_missing_card {m : Nat} (p : Snake m)
    (j a : Nat) (L : List Nat) (U : Finset Nat) (P : Nat → Bool)
    (F : Finset (Finset Nat)) (hj : 2 ≤ j) (ha : a < 9)
    (hzero : vx p 0 = 0)
    (hcoords : ∀ b, b ∈ L → b < 9 ∧ b ≠ a)
    (hfit : ∀ i, i < L.length → j + 2 * i ≤ m)
    (hvalues : ∀ i, i < L.length →
      vx p (j + 2 * i) = 2 ^ a ^^^ 2 ^ (L.getD i 0))
    (hU : ∀ b ∈ L, b ∈ U)
    (hF : ∀ b ∈ L, ∀ c ∈ L, b ≠ c →
      (∀ k, k ≤ m → vx p k ≠ 2 ^ b ^^^ 2 ^ c) →
      (P b || P c) = true → ({b,c} : Finset Nat) ∈ F) :
    L.length ≤ max 1 ((U.filter (fun b => P b = false)).card) + F.card := by
  obtain ⟨hn, hmissing⟩ :=
    CoordinateRun134.nodup_and_missing_adjacent_pairs p j a L hj ha hzero
      hcoords hfit hvalues
  apply RunLength134.length_le_outside_card_or_one_add_missing_card L U P F hn hU
  intro e he hP
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem he
  have hdrop := List.lt_length_right_of_zip hi
  simp only [List.length_drop] at hdrop
  have hi1 : i + 1 < L.length := by omega
  have hi0 : i < L.length := by omega
  have hget : ∀ t (ht : t < L.length), L.getD t 0 = L[t] := by
    intro t ht
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  have hedge : (L.getD i 0, L.getD (i + 1) 0) = e := by
    rw [hget i hi0, hget (i + 1) hi1]
    simpa only [List.getElem_zip, List.getElem_drop, Nat.add_comm] using heq
  have hmem0 : L.getD i 0 ∈ L := by
    rw [hget i hi0]
    exact List.getElem_mem hi0
  have hmem1 : L.getD (i + 1) 0 ∈ L := by
    rw [hget (i + 1) hi1]
    exact List.getElem_mem hi1
  have hpairwise : L.Pairwise (fun b c => b ≠ c) := hn
  have hne : L.getD i 0 ≠ L.getD (i + 1) 0 := by
    rw [hget i hi0, hget (i + 1) hi1]
    exact (List.pairwise_iff_getElem.mp hpairwise) i (i + 1) hi0 hi1 (by omega)
  rw [← hedge] at hP ⊢
  exact hF _ hmem0 _ hmem1 hne (hmissing i hi1) hP

#print axioms length_le_outside_card_or_one_add_missing_card
end Snake9.ActualRunBound134
