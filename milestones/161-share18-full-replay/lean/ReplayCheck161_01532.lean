import ReplayData161_0047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1532 : check start1532 proof1532 = true := by
  decide +kernel
#print axioms ok1532
theorem ok1533 : check start1533 proof1533 = true := by
  decide +kernel
#print axioms ok1533
theorem ok1534 : check start1534 proof1534 = true := by
  decide +kernel
#print axioms ok1534
theorem ok1535 : andB (check start1535 proof1535) (cpOk (replay start1535 proof1535) start1536) = true := by
  decide +kernel
#print axioms ok1535
end Snake9.ReplayFull161
