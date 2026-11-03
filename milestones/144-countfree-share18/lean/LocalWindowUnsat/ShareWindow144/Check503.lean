import LocalWindowUnsat.ShareWindow144.Data503
import LocalWindowUnsat.ShareWindow144.Data504

/-! Kernel checks of segments 2009-2012 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2009 : check start2009 proof2009 = true := by
  decide +kernel

theorem ok2010 : check start2010 proof2010 = true := by
  decide +kernel

theorem ok2011 : check start2011 proof2011 = true := by
  decide +kernel

theorem ok2012 : andB (check start2012 proof2012) (cpOk (replay start2012 proof2012) start2013) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
