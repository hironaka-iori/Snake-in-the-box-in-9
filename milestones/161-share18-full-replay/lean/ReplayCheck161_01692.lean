import ReplayData161_0052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1692 : check start1692 proof1692 = true := by
  decide +kernel
#print axioms ok1692
theorem ok1693 : check start1693 proof1693 = true := by
  decide +kernel
#print axioms ok1693
theorem ok1694 : check start1694 proof1694 = true := by
  decide +kernel
#print axioms ok1694
theorem ok1695 : andB (check start1695 proof1695) (cpOk (replay start1695 proof1695) start1696) = true := by
  decide +kernel
#print axioms ok1695
end Snake9.ReplayFull161
