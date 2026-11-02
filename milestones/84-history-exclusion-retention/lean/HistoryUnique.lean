import HistoryRealizations
import HistoryWindow

namespace Snake9.History84
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphInterpretation74 Snake9.CountFreeAdapter73
set_option maxHeartbeats 2000000

theorem realization_unique (sig expected cs : List Nat)
    (htable : realizationTable sig expected = true)
    (hlen : cs.length = 11)
    (hprefix : cs.take 9 = extensions.getD (sig.getD 0 0) [])
    (hsmall : ∀ d ∈ cs, d < 9)
    (hrgs : isRGS cs 0 = true) (hind : inducedPattern cs = true)
    (hreal : realizes sig cs = true) : cs = expected := by
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
    ((extensions.getD (sig.getD 0 0) [] ++ [a,b]) == expected)) = true at h
  rw [← heq] at h
  simpa [hrgs,hind,hreal] using h

theorem actual_canonical_small {m : Nat} (p : Snake m) (r n : Nat)
    (hr : r+n ≤ m) : ∀ d ∈ canon (dsOf p r n), d < 9 := by
  obtain ⟨u,_,_,hu,hcs⟩ := actual_canonical_frame p r n hr
  intro d hd
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hd
  have hin : i < n := by simpa only [length_canon,length_dsOf] using hi
  have h := (hcs i hin).1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [he] at h
  omega

theorem emitted_unique_word {m : Nat} (p : Snake m) (r : Nat)
    (sig expected : List Nat) (hr : r+9 ≤ m) (hlen : sig.length = 3)
    (htable : realizationTable sig expected = true)
    (hemit : sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++ [directionId p r]) :
    2 ≤ r ∧ canon (dsOf p (r-2) 11) = expected := by
  obtain ⟨hr2,hslices⟩ := emitted_three_canonical_slices p r sig hr hlen hemit
  refine ⟨hr2, realization_unique sig expected (canon (dsOf p (r-2) 11)) htable ?_ ?_ ?_ ?_ ?_ ?_⟩
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

#print axioms realization_unique
#print axioms actual_canonical_small
#print axioms emitted_unique_word
end Snake9.History84
