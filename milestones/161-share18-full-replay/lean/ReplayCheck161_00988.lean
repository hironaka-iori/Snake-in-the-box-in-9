import ReplayData161_0030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok988 : check start988 proof988 = true := by
  decide +kernel
#print axioms ok988
theorem ok989 : check start989 proof989 = true := by
  decide +kernel
#print axioms ok989
theorem ok990 : check start990 proof990 = true := by
  decide +kernel
#print axioms ok990
theorem ok991 : andB (check start991 proof991) (cpOk (replay start991 proof991) start992) = true := by
  decide +kernel
#print axioms ok991
end Snake9.ReplayFull161
