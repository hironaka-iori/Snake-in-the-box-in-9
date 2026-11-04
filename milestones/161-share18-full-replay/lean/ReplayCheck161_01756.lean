import ReplayData161_0054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1756 : check start1756 proof1756 = true := by
  decide +kernel
#print axioms ok1756
theorem ok1757 : check start1757 proof1757 = true := by
  decide +kernel
#print axioms ok1757
theorem ok1758 : check start1758 proof1758 = true := by
  decide +kernel
#print axioms ok1758
theorem ok1759 : andB (check start1759 proof1759) (cpOk (replay start1759 proof1759) start1760) = true := by
  decide +kernel
#print axioms ok1759
end Snake9.ReplayFull161
