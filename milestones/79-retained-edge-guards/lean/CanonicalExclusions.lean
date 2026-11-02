import StateWalk
import CanonicalShareAdapter

namespace Snake9.Guards79
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 1000000

theorem actual_canonical_frame {m : Nat} (p : Snake m) (r n : Nat)
    (hr : r+n ≤ m) :
    ∃ u : List Nat, u.Nodup ∧ (∀ d ∈ u, d < 9) ∧ u.length ≤ 9 ∧
      ∀ j, j < n → (canon (dsOf p r n)).getD j 0 < u.length ∧
        u.getD ((canon (dsOf p r n)).getD j 0) 0 = dir p (r+j) := by
  let u := seenAfter [] (dsOf p r n)
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
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ u := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [length_dsOf] using hj)]
    exact List.getElem_mem _
  have hcs : ∀ j, j < n → (canon (dsOf p r n)).getD j 0 < u.length ∧
      u.getD ((canon (dsOf p r n)).getD j 0) 0 = dir p (r+j) := by
    intro j hj
    have hjlen : j < (dsOf p r n).length := by simpa [length_dsOf] using hj
    have e : (canon (dsOf p r n)).getD j 0 = idx u ((dsOf p r n).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hjlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlen]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j hj), ?_⟩
    rw [getD_idx _ _ (hmem j hj), getD_dsOf p hj]
  exact ⟨u, hu, hu9, hulen, hcs⟩

theorem canonical_interval_exclusion {m : Nat} (p : Snake m) (r n : Nat)
    (cs : List Nat) (bounds : List (Nat × Nat))
    (hr : r+n ≤ m) (hlen : bounds.length+1 = n)
    (hshape : canon (dsOf p r n) = cs)
    (href : Refuted (winOf cs) bounds)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) : False := by
  obtain ⟨u, hu, hu9, hulen, hcs⟩ := actual_canonical_frame p r n hr
  have hsp := mkPerm_spec hu hu9 hulen
  have href' : Refuted (winOf (canon (dsOf p r n))) bounds := by
    simpa only [hshape] using href
  apply refuted_bridge p (mkPerm u) r href' (canon_winOf _)
    (by simpa only [length_canon, length_dsOf] using hlen)
    (by simpa only [length_canon, length_dsOf] using hr)
  · intro j hj
    have hjn : j < n := by simpa only [length_canon, length_dsOf] using hj
    obtain ⟨hi, hd⟩ := hcs j hjn
    rw [← hd]
    exact hsp _ hi
  · exact hb

theorem canonical_symbol_exclusion {m : Nat} (p : Snake m) (r n : Nat)
    (cs syms : List Nat) (hr : r+n ≤ m) (hn : 1 ≤ n)
    (hshape : canon (dsOf p r n) = cs) (hsyms : symsOf p r n = syms)
    (href : Refuted (winOf cs) (boundsOf syms)) : False := by
  obtain ⟨u, hu, hu9, _, hcs⟩ := actual_canonical_frame p r n hr
  have hlen : syms.length+1 = n := by
    rw [← hsyms, length_symsOf]; omega
  have href' : Refuted (winOf (canon (dsOf p r n))) (boundsOf syms) := by
    simpa only [hshape] using href
  apply refuted_dir href' p r
    (by simpa only [length_canon, length_dsOf] using hlen)
    (by simpa only [length_canon, length_dsOf] using hr) hu hu9
  · simpa only [length_canon, length_dsOf] using hcs
  · intro i hi
    have hi' : i < n-1 := by rw [← hsyms, length_symsOf] at hi; exact hi
    rw [← hsyms, getD_symsOf p hi']

theorem reversed_symbol_exclusion {m : Nat} (p : Snake m) (r n : Nat)
    (cs syms : List Nat) (hr : r+n ≤ m) (hn : 1 ≤ n)
    (hshape : canon (dsOf p r n).reverse = cs)
    (hsyms : (symsOf p r n).reverse = syms)
    (href : Refuted (winOf cs) (boundsOf syms)) : False := by
  apply canonical_symbol_exclusion (revSnake p) (m-r-n) n cs syms (by omega) hn
  · rw [dsOf_rev p r n hr]; exact hshape
  · rw [symsOf_rev p r n hr]; exact hsyms
  · exact href

#print axioms actual_canonical_frame
#print axioms canonical_interval_exclusion
#print axioms canonical_symbol_exclusion
#print axioms reversed_symbol_exclusion
end Snake9.Guards79
