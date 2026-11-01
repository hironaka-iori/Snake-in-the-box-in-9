import DirectionWindowBridge
import LocalWindowShareBridge
import Mathlib.Tactic

/-! Generic dispatch of a count-free canonical share certificate. The
first-occurrence coordinate realization follows the existing window_refute
proof, without importing a particular count exclusion or share catalogue. -/
namespace Snake9.CountFreeAdapter73
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 1000000

def broadBounds : List (Nat × Nat) := List.replicate 5 (0,21)

/-- The two existing representations of the same direction block agree. -/
theorem blockList_eq_dsOf {m : Nat} (p : Snake m) (r n : Nat) (hr : r+n ≤ m) :
    blockList p r n = dsOf p r n := by
  apply List.ext_getElem
  · simp [blockList, dsOf]
  · intro j h1 h2
    have hj : j < n := by simpa [blockList] using h1
    simp only [blockList, dsOf, List.getElem_map, List.getElem_range', List.getElem_range]
    simpa using pathDir_eq_dir p (j := r+j) (by omega)

/-- A canonical six-transition refutation with only the universal count bounds
implies a share bound on every actual window with the same canonical shape. -/
theorem canonical_share_bound {m K : Nat} (p : Snake m) (r : Nat) (cs : List Nat)
    (hr : r+6 ≤ m) (hshape : canon (dsOf p r 6) = cs)
    (href : RefutedShare (winOf cs) broadBounds 12 K) :
    K+1 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  let u := seenAfter [] (dsOf p r 6)
  have hu : u.Nodup := seenAfter_nodup [] _ List.nodup_nil
  have hu9 : ∀ d ∈ u, d < 9 := by
    intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  have hulen : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hmem : ∀ j, j < 6 → (dsOf p r 6).getD j 0 ∈ u := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [length_dsOf] using hj)]
    exact List.getElem_mem _
  have hcs : ∀ j, j < 6 → (canon (dsOf p r 6)).getD j 0 < u.length ∧
      u.getD ((canon (dsOf p r 6)).getD j 0) 0 = dir p (r+j) := by
    intro j hj
    have hjlen : j < (dsOf p r 6).length := by simpa [length_dsOf] using hj
    have e : (canon (dsOf p r 6)).getD j 0 = idx u ((dsOf p r 6).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hjlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlen]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j hj), ?_⟩
    rw [getD_idx _ _ (hmem j hj), getD_dsOf p hj]
  have hsp := mkPerm_spec hu hu9 hulen
  have href' : RefutedShare (winOf (canon (dsOf p r 6))) broadBounds 12 K := by
    simpa only [hshape] using href
  have result := refuted_share_bridge p (mkPerm u) r href'
    (canon_winOf (canon (dsOf p r 6)))
    (by simp [broadBounds, length_canon, length_dsOf])
    (by simpa [length_canon, length_dsOf] using hr)
    (by
      intro j hj
      have hj6 : j < 6 := by simpa [length_canon, length_dsOf] using hj
      obtain ⟨hindex, hdir⟩ := hcs j hj6
      rw [← hdir]
      exact hsp _ hindex)
    (by
      intro i hi
      have hi5 : i < 5 := by simpa [broadBounds] using hi
      have upper := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
      interval_cases i <;> simpa [broadBounds] using upper)
  simpa [broadBounds] using result

/-- A reversed canonical match has the same five-centre share sum. -/
theorem reversed_canonical_share_bound {m K : Nat} (p : Snake m) (r : Nat) (cs : List Nat)
    (hr : r+6 ≤ m) (hshape : canon (dsOf p r 6).reverse = cs)
    (href : RefutedShare (winOf cs) broadBounds 12 K) :
    K+1 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have h := canonical_share_bound (revSnake p) (m-r-6) cs (by omega)
    (by rw [dsOf_rev p r 6 hr]; exact hshape) href
  have he := coreShare_window_rev 12 p r 5 (by omega)
  have hs : m-r-5-1 = m-r-6 := by omega
  rw [hs] at he
  rw [he] at h
  exact h

theorem share_bound_of_either_canonical_match {m K : Nat} (p : Snake m) (r : Nat)
    (cs : List Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = cs ∨ canon (dsOf p r 6).reverse = cs)
    (href : RefutedShare (winOf cs) broadBounds 12 K) :
    K+1 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  rcases hshape with h | h
  · exact canonical_share_bound p r cs hr h href
  · exact reversed_canonical_share_bound p r cs hr h href

#print axioms blockList_eq_dsOf
#print axioms canonical_share_bound
#print axioms reversed_canonical_share_bound
#print axioms share_bound_of_either_canonical_match
end Snake9.CountFreeAdapter73
