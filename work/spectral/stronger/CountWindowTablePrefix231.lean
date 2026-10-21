import CountWindowTable231

/-! Complete two-symbol prefix decomposition of the 231 count-table check. -/
namespace Snake9.CountWindowTablePrefix231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge CountWindowTable231
set_option maxHeartbeats 1000000

def prefixCovered (keys : List IntervalKey) (n : Nat) (pfx : List Nat) : Bool :=
  allRGS n 0 (fun ds => !inducedPattern ds ||
    allPositiveSyms 8 (n - 3) (fun tail => covered keys ds (pfx ++ tail)))

def prefixesCovered (keys : List IntervalKey) (n : Nat) : Bool :=
  allPositiveSyms 8 2 (prefixCovered keys n)

/-- Every positive count sequence is checked by exactly its first two symbols
and the remaining suffix. No shape or symbol is omitted by this decomposition. -/
theorem no_window {keys : List IntervalKey} {n : Nat}
    (hc : prefixesCovered keys n = true) (hf : AllRefutedIntervals keys)
    {m : Nat} (p : Snake m) (r : Nat) (hn : 3 ≤ n) (hr : r + n ≤ m) :
    wforbK6R34C7W (dsOf p r n) (symsK p 8 r n) = false := by
  let syms := symsK p 8 r n
  have hlen : syms.length = n - 1 := symsK_length p 8 r n
  have hpos : ∀ s ∈ syms, 1 ≤ s ∧ s ≤ 8 := symsK_positive p 8 r n (by decide) hr
  have hprefix := allPositiveSyms_spec 8 2 _ hc (syms.take 2)
    (by simp only [List.length_take, hlen]; omega)
    (fun s hs => hpos s (List.take_subset 2 syms hs))
  have hshape := allRGS_spec n 0 _ hprefix (canon (dsOf p r n))
    (by simp [length_canon, dsOf]) (canon_isRGS _)
  have hind : inducedPattern (canon (dsOf p r n)) = true := by
    rw [inducedPattern_canon, ← ParallelShareShapeBridge.blockList_eq_dsOf p r n hr]
    exact snake_inducedPattern_block p r n hr
  simp only [hind, Bool.not_true, Bool.false_or] at hshape
  have hcover := allPositiveSyms_spec 8 (n-3) _ hshape (syms.drop 2)
    (by simp only [List.length_drop, hlen]; omega)
    (fun s hs => hpos s (List.drop_subset 2 syms hs))
  rw [List.take_append_drop, covered_canon] at hcover
  simp only [covered, syms, no_interval_hit hf p r n (by omega) hr,
    no_reverse_interval_hit hf p r n (by omega) hr, Bool.or_false] at hcover
  simpa using hcover

#print axioms no_window
end Snake9.CountWindowTablePrefix231
