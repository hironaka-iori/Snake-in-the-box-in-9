import DirectionTables
import PrunedEnumeration
import CoverageAssembly
import WindowAutomatonBridge

namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem coverage_eight_table :
    allPruned 8 0 [] (fun c => shapes.contains c) = true := by
  exact coverage_8_root

theorem coverage_nine_table :
    allPruned 9 0 [] (fun c => extensions.contains c) = true := by
  exact coverage_9_root

theorem canonical_eight_coverage (c : List Nat) (hlen : c.length = 8)
    (hrgs : isRGS c 0 = true) (hind : inducedPattern c = true) : c ∈ shapes := by
  have h := allPruned_spec 8 0 [] _ coverage_eight_table c hlen hrgs (by simpa using hind)
  exact List.contains_iff.mp (by simpa using h)

theorem canonical_nine_coverage (c : List Nat) (hlen : c.length = 9)
    (hrgs : isRGS c 0 = true) (hind : inducedPattern c = true) : c ∈ extensions := by
  have h := allPruned_spec 9 0 [] _ coverage_nine_table c hlen hrgs (by simpa using hind)
  exact List.contains_iff.mp (by simpa using h)

theorem snake_eight_coverage {m : Nat} (p : Snake m) (r : Nat) (hr : r+8 ≤ m) :
    canon (blockList p r 8) ∈ shapes := by
  apply canonical_eight_coverage
  · simp [length_canon, blockList]
  · exact canon_isRGS _
  · rw [inducedPattern_canon]
    exact snake_inducedPattern_block p r 8 hr

theorem snake_nine_coverage {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    canon (blockList p r 9) ∈ extensions := by
  apply canonical_nine_coverage
  · simp [length_canon, blockList]
  · exact canon_isRGS _
  · rw [inducedPattern_canon]
    exact snake_inducedPattern_block p r 9 hr

#print axioms coverage_eight_table
#print axioms coverage_nine_table
#print axioms canonical_eight_coverage
#print axioms canonical_nine_coverage
#print axioms snake_eight_coverage
#print axioms snake_nine_coverage
end Snake9.Direction77
