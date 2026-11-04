import ReplayData161_0062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2000 : check start2000 proof2000 = true := by
  decide +kernel
#print axioms ok2000
theorem ok2001 : check start2001 proof2001 = true := by
  decide +kernel
#print axioms ok2001
theorem ok2002 : check start2002 proof2002 = true := by
  decide +kernel
#print axioms ok2002
theorem ok2003 : check start2003 proof2003 = true := by
  decide +kernel
#print axioms ok2003
end Snake9.ReplayFull161
