import HistoryUnique

/-!
Finite covers of the canonical eleven-direction words compatible with an
emitted three-direction-ID signature. Concrete tables and per-word geometric
share bounds are supplied separately. This source awaits compilation.
-/

namespace Snake9.HistoryShare94
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphInterpretation74
open Snake9.CountFreeAdapter73 Snake9.History84

set_option maxHeartbeats 2000000

/-- Every admissible two-coordinate continuation of the first nine-direction
word must occur in the supplied cover. The table makes no share claim. -/
def shareCoverTable (sig : List Nat) (expectedWords : List (List Nat)) : Bool :=
  allBelow 9 fun a => allBelow 9 fun b =>
    let cs := extensions.getD (sig.getD 0 0) [] ++ [a,b]
    !isRGS cs 0 || !inducedPattern cs || !realizes sig cs || expectedWords.contains cs

/-- The generic realization hypotheses are the same as in realization_unique;
the conclusion is membership in a cover rather than equality to one word. -/
theorem share_cover_mem (sig : List Nat) (expectedWords : List (List Nat))
    (cs : List Nat) (htable : shareCoverTable sig expectedWords = true)
    (hlen : cs.length = 11)
    (hprefix : cs.take 9 = extensions.getD (sig.getD 0 0) [])
    (hsmall : ∀ d ∈ cs, d < 9)
    (hrgs : isRGS cs 0 = true) (hind : inducedPattern cs = true)
    (hreal : realizes sig cs = true) : cs ∈ expectedWords := by
  have htail : (cs.drop 9).length = 2 := by simp [hlen]
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp htail
  have heq : cs = extensions.getD (sig.getD 0 0) [] ++ [a,b] := by
    rw [← hprefix, ← hab]
    exact (List.take_append_drop 9 cs).symm
  have ha : a < 9 := hsmall a (by rw [heq]; simp)
  have hb : b < 9 := hsmall b (by rw [heq]; simp)
  have h := allBelow_spec 9 _ (allBelow_spec 9 _ htable a ha) b hb
  change (!isRGS (extensions.getD (sig.getD 0 0) [] ++ [a,b]) 0 ||
    !inducedPattern (extensions.getD (sig.getD 0 0) [] ++ [a,b]) ||
    !realizes sig (extensions.getD (sig.getD 0 0) [] ++ [a,b]) ||
    expectedWords.contains (extensions.getD (sig.getD 0 0) [] ++ [a,b])) = true at h
  rw [← heq] at h
  have hcontains : expectedWords.contains cs = true := by
    simpa [hrgs,hind,hreal] using h
  exact List.contains_iff_mem.mp hcontains

/-- An emitted signature places the actual canonical eleven-direction window
in its checked cover. The history argument also supplies the start bound. -/
theorem emitted_word_mem {m : Nat} (p : Snake m) (r : Nat)
    (sig : List Nat) (expectedWords : List (List Nat))
    (hr : r+9 ≤ m) (hlen : sig.length = 3)
    (htable : shareCoverTable sig expectedWords = true)
    (hemit : sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++
      [directionId p r]) :
    2 ≤ r ∧ canon (dsOf p (r-2) 11) ∈ expectedWords := by
  obtain ⟨hr2,hslices⟩ := emitted_three_canonical_slices p r sig hr hlen hemit
  refine ⟨hr2, share_cover_mem sig expectedWords
    (canon (dsOf p (r-2) 11)) htable ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp [length_canon,length_dsOf]
  · rw [canon_take_exact]
    simpa only [List.drop_zero,canon_canon_take] using hslices 0 (by omega)
  · exact actual_canonical_small p (r-2) 11 (by omega)
  · exact canon_isRGS _
  · rw [inducedPattern_canon, ← blockList_eq_dsOf p (r-2) 11 (by omega)]
    exact snake_inducedPattern_block p (r-2) 11 (by omega)
  · unfold realizes
    have h0 := hslices 0 (by omega)
    simp only [List.drop_zero] at h0
    rw [h0, hslices 1 (by omega), hslices 2 (by omega)]
    simp

/-- A per-word geometric premise. An eleven-direction window starting at s
charges the five centres s+6 through s+10. This definition supplies no proof
of the bound for any concrete word. -/
def WordShareBound (cs : List Nat) (L : Nat) : Prop :=
  ∀ {m : Nat} (p : Snake m) (s : Nat), s+11 ≤ m →
    canon (dsOf p s 11) = cs →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (s+(i+6))).sum

/-- Dispatch checked cover membership to a supplied bound for every covered
word. The centres become r+4 through r+8 because the window starts at r-2. -/
theorem emitted_five_centre_share {m : Nat} (p : Snake m) (r : Nat)
    (sig : List Nat) (expectedWords : List (List Nat)) (L : Nat)
    (hr : r+9 ≤ m) (hlen : sig.length = 3)
    (htable : shareCoverTable sig expectedWords = true)
    (hemit : sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++
      [directionId p r])
    (hwords : ∀ cs ∈ expectedWords, WordShareBound cs L) :
    L ≤ ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  obtain ⟨hr2,hmem⟩ := emitted_word_mem p r sig expectedWords hr hlen htable hemit
  have hbound := (hwords _ hmem) p (r-2) (by omega) rfl
  have hshift : ∀ i : Nat, r-2+(i+6) = r+(i+4) := by
    intro i
    omega
  simpa only [hshift] using hbound

#print axioms share_cover_mem
#print axioms emitted_word_mem
#print axioms emitted_five_centre_share

end Snake9.HistoryShare94
