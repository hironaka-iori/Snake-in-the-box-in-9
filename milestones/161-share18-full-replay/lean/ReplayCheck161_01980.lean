import ReplayData161_0061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1980 : check start1980 proof1980 = true := by
  decide +kernel
#print axioms ok1980
theorem ok1981 : check start1981 proof1981 = true := by
  decide +kernel
#print axioms ok1981
theorem ok1982 : check start1982 proof1982 = true := by
  decide +kernel
#print axioms ok1982
theorem ok1983 : andB (check start1983 proof1983) (cpOk (replay start1983 proof1983) start1984) = true := by
  decide +kernel
#print axioms ok1983
end Snake9.ReplayFull161
