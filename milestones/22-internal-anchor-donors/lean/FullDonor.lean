import PairedSeed

namespace Snake9.PairedSeed
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def fullDonor : Snake 191 := alignSnake witness

theorem fullDonor_start : fullDonor.vertex 0 = 41 := by decide
theorem fullDonor_anchor : fullDonor.vertex ⟨190, by decide⟩ = 67 := by decide
theorem fullDonor_end : fullDonor.vertex (Fin.last 191) = 83 := by decide

theorem fullDonor_prefix : takePrefix fullDonor (show 190 ≤ 191 by decide) = pairedWitness := by
  rfl

#print axioms fullDonor_start
#print axioms fullDonor_anchor
#print axioms fullDonor_end
#print axioms fullDonor_prefix
end Snake9.PairedSeed
