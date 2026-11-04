import ReplayData161_0062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2008 : check start2008 proof2008 = true := by
  decide +kernel
#print axioms ok2008
theorem ok2009 : check start2009 proof2009 = true := by
  decide +kernel
#print axioms ok2009
theorem ok2010 : check start2010 proof2010 = true := by
  decide +kernel
#print axioms ok2010
theorem ok2011 : check start2011 proof2011 = true := by
  decide +kernel
#print axioms ok2011
end Snake9.ReplayFull161
