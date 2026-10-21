import CountWindowFour231.Data
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Snake9.CountWindowFour231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
open CountWindowTable231 CountWindowTablePrefix231

theorem table_checked : tableCovered keys 5 = true := by decide +kernel

theorem no_count_window (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m)
    (r : Nat) (hr : r + 5 ≤ m) :
    wforbK6R34C7W (dsOf p r 5) (symsK p 8 r 5) = false :=
  CountWindowTable231.no_window table_checked h p r (by decide) hr

/-- The original aggregate hw4 premise; concrete refutations remain explicit. -/
theorem hw4_of_counts (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m) :
    ∀ r, r + 5 ≤ m → wforbK6R34C7W
      [pathDir p r, pathDir p (r+1), pathDir p (r+2), pathDir p (r+3), pathDir p (r+4)]
      [symK 8 (countSeq p (r+1)), symK 8 (countSeq p (r+2)), symK 8 (countSeq p (r+3)), symK 8 (countSeq p (r+4))] = false := by
  intro r hr
  rw [countSeq_eq_coreAlpha p (r+1) (by omega),
    countSeq_eq_coreAlpha p (r+2) (by omega),
    countSeq_eq_coreAlpha p (r+3) (by omega),
    countSeq_eq_coreAlpha p (r+4) (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega)]
  exact no_count_window h p r hr

#print axioms table_checked
#print axioms no_count_window
#print axioms hw4_of_counts
end Snake9.CountWindowFour231
