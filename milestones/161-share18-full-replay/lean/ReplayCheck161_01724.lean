import ReplayData161_0053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1724 : check start1724 proof1724 = true := by
  decide +kernel
#print axioms ok1724
theorem ok1725 : check start1725 proof1725 = true := by
  decide +kernel
#print axioms ok1725
theorem ok1726 : check start1726 proof1726 = true := by
  decide +kernel
#print axioms ok1726
theorem ok1727 : andB (check start1727 proof1727) (cpOk (replay start1727 proof1727) start1728) = true := by
  decide +kernel
#print axioms ok1727
end Snake9.ReplayFull161
