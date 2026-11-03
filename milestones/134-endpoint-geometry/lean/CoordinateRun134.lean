import MissingPair134

namespace Snake9.CoordinateRun134
open Snake9.LocalWindow

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Coordinates representing every second vertex of an actual snake are distinct.
Each adjacent coordinate pair gives a pair vertex absent from the whole snake. -/
theorem nodup_and_missing_adjacent_pairs {m : Nat} (p : Snake m)
    (j a : Nat) (L : List Nat) (hj : 2 ≤ j) (ha : a < 9)
    (hzero : vx p 0 = 0)
    (hcoords : ∀ b, b ∈ L → b < 9 ∧ b ≠ a)
    (hfit : ∀ i, i < L.length → j + 2 * i ≤ m)
    (hvalues : ∀ i, i < L.length →
      vx p (j + 2 * i) = 2 ^ a ^^^ 2 ^ (L.getD i 0)) :
    L.Nodup ∧
      ∀ i, i + 1 < L.length →
        ∀ k, k ≤ m →
          vx p k ≠ 2 ^ (L.getD i 0) ^^^ 2 ^ (L.getD (i + 1) 0) := by
  have hget : ∀ i (hi : i < L.length), L.getD i 0 = L[i] := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hinj : ∀ i, i < L.length → ∀ t, t < L.length →
      L.getD i 0 = L.getD t 0 → i = t := by
    intro i hi t ht heq
    have hvertices : vx p (j + 2 * i) = vx p (j + 2 * t) := by
      rw [hvalues i hi, hvalues t ht, heq]
    have hindices := vx_inj p (hfit i hi) (hfit t ht) hvertices
    omega
  have hnodup : L.Nodup := by
    change L.Pairwise (fun x y => x ≠ y)
    apply List.pairwise_iff_getElem.2
    intro i t hi ht hit heq
    have hsame : L.getD i 0 = L.getD t 0 := by
      rw [hget i hi, hget t ht]
      exact heq
    have := hinj i hi t ht hsame
    omega
  refine ⟨hnodup, ?_⟩
  intro i hi
  have hi0 : i < L.length := by omega
  have hmem0 : L.getD i 0 ∈ L := by
    rw [hget i hi0]
    exact List.getElem_mem hi0
  have hmem1 : L.getD (i + 1) 0 ∈ L := by
    rw [hget (i + 1) hi]
    exact List.getElem_mem hi
  have hc0 := hcoords _ hmem0
  have hc1 := hcoords _ hmem1
  have hdifferent : L.getD i 0 ≠ L.getD (i + 1) 0 := by
    intro heq
    have := hinj i hi0 (i + 1) hi heq
    omega
  have hlast := hfit (i + 1) hi
  have hright : vx p (j + 2 * i + 2) =
      2 ^ a ^^^ 2 ^ (L.getD (i + 1) 0) := by
    have hindex : j + 2 * i + 2 = j + 2 * (i + 1) := by omega
    rw [hindex]
    exact hvalues (i + 1) hi
  have hmissing := MissingPair134.middle_and_missing_pair p (j + 2 * i) a
    (L.getD i 0) (L.getD (i + 1) 0) (by omega) (by omega)
    ha hc0.1 hc1.1 (Ne.symm hc0.2) (Ne.symm hc1.2) hdifferent
    hzero (hvalues i hi0) hright
  exact hmissing.2

#print axioms nodup_and_missing_adjacent_pairs
end Snake9.CoordinateRun134
