import ReplayData161_0057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1852 : check start1852 proof1852 = true := by
  decide +kernel
#print axioms ok1852
theorem ok1853 : check start1853 proof1853 = true := by
  decide +kernel
#print axioms ok1853
theorem ok1854 : check start1854 proof1854 = true := by
  decide +kernel
#print axioms ok1854
theorem ok1855 : andB (check start1855 proof1855) (cpOk (replay start1855 proof1855) start1856) = true := by
  decide +kernel
#print axioms ok1855
end Snake9.ReplayFull161
