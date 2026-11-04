import ReplayData161_0062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2012 : check start2012 proof2012 = true := by
  decide +kernel
#print axioms ok2012
theorem ok2013 : check start2013 proof2013 = true := by
  decide +kernel
#print axioms ok2013
theorem ok2014 : check start2014 proof2014 = true := by
  decide +kernel
#print axioms ok2014
theorem ok2015 : andB (check start2015 proof2015) (cpOk (replay start2015 proof2015) start2016) = true := by
  decide +kernel
#print axioms ok2015
end Snake9.ReplayFull161
