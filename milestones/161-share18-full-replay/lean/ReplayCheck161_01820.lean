import ReplayData161_0056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1820 : check start1820 proof1820 = true := by
  decide +kernel
#print axioms ok1820
theorem ok1821 : check start1821 proof1821 = true := by
  decide +kernel
#print axioms ok1821
theorem ok1822 : check start1822 proof1822 = true := by
  decide +kernel
#print axioms ok1822
theorem ok1823 : andB (check start1823 proof1823) (cpOk (replay start1823 proof1823) start1824) = true := by
  decide +kernel
#print axioms ok1823
end Snake9.ReplayFull161
