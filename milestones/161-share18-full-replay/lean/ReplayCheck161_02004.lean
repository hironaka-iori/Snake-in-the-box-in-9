import ReplayData161_0062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2004 : check start2004 proof2004 = true := by
  decide +kernel
#print axioms ok2004
theorem ok2005 : check start2005 proof2005 = true := by
  decide +kernel
#print axioms ok2005
theorem ok2006 : check start2006 proof2006 = true := by
  decide +kernel
#print axioms ok2006
theorem ok2007 : check start2007 proof2007 = true := by
  decide +kernel
#print axioms ok2007
end Snake9.ReplayFull161
