import ReplayData161_0027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok892 : check start892 proof892 = true := by
  decide +kernel
#print axioms ok892
theorem ok893 : check start893 proof893 = true := by
  decide +kernel
#print axioms ok893
theorem ok894 : check start894 proof894 = true := by
  decide +kernel
#print axioms ok894
theorem ok895 : andB (check start895 proof895) (cpOk (replay start895 proof895) start896) = true := by
  decide +kernel
#print axioms ok895
end Snake9.ReplayFull161
