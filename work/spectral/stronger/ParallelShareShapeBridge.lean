import DirectionWindowBridge
import ParallelShareBridge

/-! Complete seven-direction shape coverage and canonical share transport.
The shape order is exactly that of the frozen 34-model share batch.
The family theorem keeps its local refutations explicit until that batch is joined.
-/
namespace Snake9.ParallelShareShapeBridge
open LocalWindow DirectionWindow WindowAutomaton
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def shapes : List (List Nat) :=
  [[0,1,2,0,3,1,0], [0,1,2,0,3,1,4], [0,1,2,0,3,2,4],
   [0,1,2,0,3,4,0], [0,1,2,0,3,4,1], [0,1,2,0,3,4,2], [0,1,2,0,3,4,5],
   [0,1,2,3,0,1,4], [0,1,2,3,0,2,4], [0,1,2,3,0,4,1], [0,1,2,3,0,4,2],
   [0,1,2,3,0,4,3], [0,1,2,3,0,4,5], [0,1,2,3,1,0,4], [0,1,2,3,1,4,0],
   [0,1,2,3,1,4,2], [0,1,2,3,1,4,3], [0,1,2,3,1,4,5], [0,1,2,3,4,0,1],
   [0,1,2,3,4,0,2], [0,1,2,3,4,0,3], [0,1,2,3,4,0,5], [0,1,2,3,4,1,0],
   [0,1,2,3,4,1,2], [0,1,2,3,4,1,3], [0,1,2,3,4,1,5], [0,1,2,3,4,2,0],
   [0,1,2,3,4,2,1], [0,1,2,3,4,2,5], [0,1,2,3,4,5,0], [0,1,2,3,4,5,1],
   [0,1,2,3,4,5,2], [0,1,2,3,4,5,3], [0,1,2,3,4,5,6]]

theorem shape_table_checked :
    (shapes.length == 34 && shapes.all (fun ds =>
      ds.length == 7 && isRGS ds 0 && inducedPattern ds)) = true := by
  decide +kernel

theorem coverage_checked :
    allRGS 7 0 (fun ds => !inducedPattern ds || decide (ds ∈ shapes)) = true := by
  decide +kernel

theorem blockList_eq_dsOf {m : Nat} (p : Snake m) (r n : Nat) (hr : r + n ≤ m) :
    blockList p r n = dsOf p r n := by
  apply List.ext_getElem
  · simp [blockList, dsOf]
  · intro j hj hj'
    have hjn : j < n := by simpa [dsOf] using hj'
    simp only [blockList, dsOf, List.getElem_map, List.getElem_range', List.getElem_range]
    simpa using (pathDir_eq_dir p (j := r + j) (by omega))

/-- Every actual seven-edge snake window has one of the 34 certified shapes. -/
theorem window_shape_mem {m : Nat} (p : Snake m) (r : Nat) (hr : r + 7 ≤ m) :
    canon (blockList p r 7) ∈ shapes := by
  have h := allRGS_spec 7 0 _ coverage_checked (canon (blockList p r 7))
    (by simp [length_canon, blockList]) (canon_isRGS _)
  rw [inducedPattern_canon, snake_inducedPattern_block p r 7 hr] at h
  simpa using h

/-- Canonicalisation supplies its own injective coordinate relabelling. -/
theorem refuted_canonical_window {m : Nat} (p : Snake m) (r n cap : Nat)
    (hn : 1 ≤ n) (hr : r + n ≤ m)
    (href : RefutedParallel (winOf (canon (blockList p r n)))
      (List.replicate (n - 1) (0, 21)) cap) :
    cap + 1 ≤ ((List.range (n - 1)).map fun i => coreParallelShare p (r + i + 1)).sum := by
  rw [blockList_eq_dsOf p r n hr] at href
  have hlen := length_dsOf p r n
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ seenAfter [] (dsOf p r n) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have href' : RefutedParallel (winOf (canon (dsOf p r n)))
      (List.replicate ((canon (dsOf p r n)).length - 1) (0, 21)) cap := by
    simpa only [length_canon, hlen] using href
  have h := refuted_parallel_shape href' p r (u := seenAfter [] (dsOf p r n))
    (by rw [length_canon, hlen]; exact hn)
    (by rw [length_canon, hlen]; exact hr)
    (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_
  · simpa only [length_canon, hlen] using h
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro j hj
    rw [length_canon] at hj
    have e : (canon (dsOf p r n)).getD j 0 =
        idx (seenAfter [] (dsOf p r n)) ((dsOf p r n).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]

/-- The only remaining premise here is the explicit family of local refutations. -/
theorem window_share_ge_21_of_family
    (hfamily : ∀ ds ∈ shapes, RefutedParallel (winOf ds) (List.replicate 6 (0, 21)) 20)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r + 7 ≤ m) :
    21 ≤ ((List.range 6).map fun i => coreParallelShare p (r + i + 1)).sum :=
  refuted_canonical_window p r 7 20 (by decide) hr
    (hfamily _ (window_shape_mem p r hr))

#print axioms coverage_checked
#print axioms window_shape_mem
#print axioms refuted_canonical_window
#print axioms window_share_ge_21_of_family
end Snake9.ParallelShareShapeBridge
