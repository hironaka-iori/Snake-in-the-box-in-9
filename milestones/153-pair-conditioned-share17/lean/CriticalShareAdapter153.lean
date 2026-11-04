import CanonicalShareAdapter
import Share153.Semantics153

/-!
Pending source: this module has not been checked in Lean.
The local certificate remains an explicit Unsat premise.
The five count intervals are transported without clipping or weakening.
-/
namespace Snake9.CriticalShare153
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- An arbitrary list of five count intervals on a canonical six-transition window. -/
theorem canonical_share_bound_with_bounds {m M K : Nat} (p : Snake m)
    (r : Nat) (cs : List Nat) (bounds : List (Nat × Nat))
    (hlen : bounds.length = 5) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = cs)
    (hb : ∀ i, i < 5 →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2)
    (href : RefutedShare (winOf cs) bounds M K) :
    K+1 ≤ ((List.range 5).map fun i => coreShare M p (r+i+1)).sum := by
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
  have href' : RefutedShare (winOf (canon (dsOf p r 6))) bounds M K := by
    simpa only [hshape] using href
  have result := refuted_share_bridge p (mkPerm u) r href'
    (canon_winOf (canon (dsOf p r 6)))
    (by simp [hlen, length_canon, length_dsOf])
    (by simpa [length_canon, length_dsOf] using hr)
    (by
      intro j hj
      have hj6 : j < 6 := by simpa [length_canon, length_dsOf] using hj
      obtain ⟨hindex, hdir⟩ := hcs j hj6
      rw [← hdir]
      exact hsp _ hindex)
    (by
      intro i hi
      exact hb i (by simpa only [hlen] using hi))
  simpa only [hlen] using result

/-- Interval i is imposed on original centre r+(4-i)+1 in the reversed orientation. -/
theorem reversed_share_bound_with_bounds {m M K : Nat} (p : Snake m)
    (r : Nat) (cs : List Nat) (bounds : List (Nat × Nat))
    (hlen : bounds.length = 5) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6).reverse = cs)
    (hb : ∀ i, i < 5 →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+(4-i)+1) ∧
      coreAlpha p (r+(4-i)+1) ≤ (bounds.getD i (0,21)).2)
    (href : RefutedShare (winOf cs) bounds M K) :
    K+1 ≤ ((List.range 5).map fun i => coreShare M p (r+i+1)).sum := by
  have h := canonical_share_bound_with_bounds (revSnake p) (m-r-6)
    cs bounds hlen (by omega)
    (by rw [dsOf_rev p r 6 hr]; exact hshape)
    (by
      intro i hi
      rw [coreAlpha_rev p (by omega)]
      have he : m - (m-r-6+i+1) = r+(4-i)+1 := by omega
      simpa only [he] using hb i hi)
    href
  have he := coreShare_window_rev M p r 5 (by omega)
  have hs : m-r-5-1 = m-r-6 := by omega
  rw [hs] at he
  rw [he] at h
  exact h

/-- Exact critical counts; a reversed direction match uses reversed counts. -/
theorem share17_of_core_unsat
    (hunsat : Unsat ShareWindow153.cnf)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hcase :
      (canon (dsOf p r 6) = [0,1,2,0,3,2] ∧
        coreAlpha p (r+1) = 4 ∧ coreAlpha p (r+2) = 4 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) = 5 ∧
        coreAlpha p (r+5) = 3) ∨
      (canon (dsOf p r 6).reverse = [0,1,2,0,3,2] ∧
        coreAlpha p (r+1) = 3 ∧ coreAlpha p (r+2) = 5 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) = 4 ∧
        coreAlpha p (r+5) = 4)) :
    17 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have href : RefutedShare (winOf [0,1,2,0,3,2])
      [(4,4),(4,4),(4,4),(5,5),(3,3)] 12 16 := by
    simpa only [ShareWindow153.window, ShareWindow153.bounds,
      ShareWindow153.resolution, ShareWindow153.cap, winOf] using
      ShareWindow153.local_share17_of_core_unsat153 hunsat
  rcases hcase with ⟨hshape,h1,h2,h3,h4,h5⟩ | ⟨hshape,h1,h2,h3,h4,h5⟩
  · exact canonical_share_bound_with_bounds p r [0,1,2,0,3,2]
      [(4,4),(4,4),(4,4),(5,5),(3,3)] (by decide) hr hshape
      (by
        intro i hi
        interval_cases i <;> simp [Nat.add_assoc,h1,h2,h3,h4,h5])
      href
  · exact reversed_share_bound_with_bounds p r [0,1,2,0,3,2]
      [(4,4),(4,4),(4,4),(5,5),(3,3)] (by decide) hr hshape
      (by
        intro i hi
        interval_cases i <;> simp [Nat.add_assoc,h1,h2,h3,h4,h5])
      href

#print axioms canonical_share_bound_with_bounds
#print axioms reversed_share_bound_with_bounds
#print axioms share17_of_core_unsat
end Snake9.CriticalShare153
