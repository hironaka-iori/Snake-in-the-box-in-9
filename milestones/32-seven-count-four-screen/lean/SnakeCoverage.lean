import ParityCoverage
import DirectionWindowBridge

namespace Snake9.FourRun
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem dsOf_eq_blockList {m : Nat} (p : Snake m) (r n : Nat) (hr : r+n ≤ m) :
    dsOf p r n = blockList p r n := by
  apply List.ext_getElem
  · simp [dsOf, blockList]
  · intro j h1 h2
    simp only [dsOf, List.length_map, List.length_range] at h1
    simp only [dsOf, blockList, List.getElem_map, List.getElem_range, List.getElem_range']
    simpa only [Nat.one_mul] using (pathDir_eq_dir p (j := r+j) (by omega)).symm

theorem snake_pattern {m : Nat} (p : Snake m) (r : Nat) (hr : r+7 ≤ m) :
    canon (dsOf p r 7) ∈ patterns := by
  apply normalized_covered _ (length_dsOf p r 7)
  rw [dsOf_eq_blockList p r 7 hr]
  exact snake_inducedPattern_block p r 7 hr

/-- The only outstanding premises are the 34 finite refutations. -/
theorem no_six_fours_of_refuted
    (hall : ∀ cs ∈ patterns, Refuted (winOf cs) (boundsOf (List.replicate 6 4)))
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+7 ≤ m)
    (hc : ∀ i, i < 6 → coreAlpha p (r+i+1) = 4) : False := by
  have href := hall _ (snake_pattern p r hr)
  have hlen := length_dsOf p r 7
  have hmem : ∀ j, j < 7 → (dsOf p r 7).getD j 0 ∈ seenAfter [] (dsOf p r 7) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine refuted_dir href p r (u := seenAfter [] (dsOf p r 7))
    (by rw [length_canon]; simp [hlen])
    (by rw [length_canon]; omega) (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro j hj
    rw [length_canon] at hj
    have e : (canon (dsOf p r 7)).getD j 0 =
        idx (seenAfter [] (dsOf p r 7)) ((dsOf p r 7).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    have hi6 : i < 6 := by simpa using hi
    rw [hc i hi6]
    have hget : (List.replicate 6 4).getD i 0 = 4 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_replicate]
    rw [hget]
    rfl

#print axioms dsOf_eq_blockList
#print axioms snake_pattern
#print axioms no_six_fours_of_refuted
end Snake9.FourRun
