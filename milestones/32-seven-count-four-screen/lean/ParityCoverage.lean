import FamilyCoverage
import WindowAutomatonLemmas

namespace Snake9.FourRun
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def parityCovered (ds : List Nat) : Bool := !inducedPattern ds || decide (ds ∈ patterns)

theorem parity_table : allRGS 7 0 parityCovered = true := by decide +kernel

theorem normalized_covered (ds : List Nat) (hn : ds.length = 7)
    (hi : inducedPattern ds = true) : canon ds ∈ patterns := by
  have h := allRGS_spec 7 0 parityCovered parity_table (canon ds)
    (by rw [length_canon, hn]) (canon_isRGS ds)
  have he : decide (canon ds ∈ patterns) = true := by
    simpa [parityCovered, inducedPattern_canon, hi] using h
  exact of_decide_eq_true he

#print axioms parity_table
#print axioms normalized_covered
end Snake9.FourRun
