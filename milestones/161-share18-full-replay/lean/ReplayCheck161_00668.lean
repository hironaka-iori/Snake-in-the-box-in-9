import ReplayData161_0020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok668 : check start668 proof668 = true := by
  decide +kernel
#print axioms ok668
theorem ok669 : check start669 proof669 = true := by
  decide +kernel
#print axioms ok669
theorem ok670 : check start670 proof670 = true := by
  decide +kernel
#print axioms ok670
theorem ok671 : andB (check start671 proof671) (cpOk (replay start671 proof671) start672) = true := by
  decide +kernel
#print axioms ok671
end Snake9.ReplayFull161
