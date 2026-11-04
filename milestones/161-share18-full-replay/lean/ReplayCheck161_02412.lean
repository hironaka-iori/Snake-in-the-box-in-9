import ReplayData161_0075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2412 : check start2412 proof2412 = true := by
  decide +kernel
#print axioms ok2412
theorem ok2413 : check start2413 proof2413 = true := by
  decide +kernel
#print axioms ok2413
theorem ok2414 : andB (check start2414 proof2414) (hasEmpty (replay start2414 proof2414) 12120) = true := by
  decide +kernel
#print axioms ok2414
end Snake9.ReplayFull161
