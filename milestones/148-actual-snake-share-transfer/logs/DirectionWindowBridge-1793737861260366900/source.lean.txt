import WindowAutomatonLemmas
import WindowAutomatonBridge
import LocalWindowDirBridge

namespace Snake9.DirectionWindow
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton

set_option maxHeartbeats 1000000

theorem getD_idx : ∀ (u : List Nat) (d : Nat), d ∈ u → u.getD (idx u d) 0 = d
  | [], _, h => absurd h List.not_mem_nil
  | a :: u, d, h => by
    unfold idx
    by_cases had : a = d
    · rw [if_pos had]; simp [had]
    · rw [if_neg had]
      have hd : d ∈ u := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm had
        · exact h
      simp only [List.getD_cons_succ]
      exact getD_idx u d hd

theorem seenAfter_nodup : ∀ (seen ds : List Nat), seen.Nodup → (seenAfter seen ds).Nodup
  | _, [], h => h
  | seen, d :: ds, h => by
    unfold seenAfter
    apply seenAfter_nodup
    split
    · exact h
    · rename_i hd
      show List.Pairwise (· ≠ ·) (seen ++ [d])
      rw [List.pairwise_append]
      refine ⟨h, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro e
      subst e
      exact hd ha

theorem mem_seenAfter_cases : ∀ (seen ds : List Nat) (d : Nat),
    d ∈ seenAfter seen ds → d ∈ seen ∨ d ∈ ds
  | _, [], _, h => Or.inl h
  | seen, a :: ds, d, h => by
    unfold seenAfter at h
    rcases mem_seenAfter_cases _ ds d h with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h
          subst h
          exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

section Window
variable {m : Nat} (p : Snake m)

/-- Directions of the `n` path steps starting at index `r`. -/
def dsOf (r n : Nat) : List Nat := (List.range n).map (fun j => dir p (r + j))

/-- Lumped singleton counts of the `n - 1` centres of that window. -/
def symsOf (r n : Nat) : List Nat :=
  (List.range (n - 1)).map (fun i => symC (coreAlpha p (r + i + 1)))

theorem length_dsOf (r n : Nat) : (dsOf p r n).length = n := by simp [dsOf]

theorem length_symsOf (r n : Nat) : (symsOf p r n).length = n - 1 := by simp [symsOf]

theorem getD_dsOf {r n j : Nat} (hj : j < n) : (dsOf p r n).getD j 0 = dir p (r + j) := by
  simp [dsOf, List.getD_eq_getElem?_getD, hj]

theorem getD_symsOf {r n i : Nat} (hi : i < n - 1) :
    (symsOf p r n).getD i 0 = symC (coreAlpha p (r + i + 1)) := by
  simp [symsOf, List.getD_eq_getElem?_getD, hi]

theorem dsOf_rev (r n : Nat) (hr : r + n ≤ m) :
    dsOf (revSnake p) (m - r - n) n = (dsOf p r n).reverse := by
  apply List.ext_getElem
  · simp [dsOf]
  · intro j h1 h2
    simp only [dsOf, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    simp only [dsOf, List.length_map, List.length_range] at h1
    rw [dir_rev p (by omega)]
    congr 1
    omega

theorem symsOf_rev (r n : Nat) (hr : r + n ≤ m) :
    symsOf (revSnake p) (m - r - n) n = (symsOf p r n).reverse := by
  apply List.ext_getElem
  · simp [symsOf]
  · intro i h1 h2
    simp only [symsOf, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    simp only [symsOf, List.length_map, List.length_range] at h1
    rw [coreAlpha_rev p (by omega)]
    congr 2
    omega

end Window

theorem pathDir_eq_dir {m : Nat} (p : Snake m) {j : Nat} (hj : j < m) : pathDir p j = dir p j := by
  have h1 : j + 1 < m + 1 := by omega
  have hadj : Adj (p.vertex ⟨j, by omega⟩) (p.vertex ⟨j + 1, h1⟩) :=
    (path_adj_iff p _ _).mpr (Or.inl rfl)
  have he := WindowAutomaton.adj_dirOf _ _ hadj
  unfold dir vx
  rw [dif_pos (by omega), dif_pos h1, he, dirOfStep_xor]
  unfold pathDir
  rw [dif_pos h1]


#print axioms getD_idx
#print axioms seenAfter_nodup
#print axioms mem_seenAfter_cases
#print axioms dsOf_rev
#print axioms pathDir_eq_dir
end Snake9.DirectionWindow
