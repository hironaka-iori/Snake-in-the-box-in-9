import LocalWindowUnsat.ShareWindow144.Data502
import LocalWindowUnsat.ShareWindow144.Data503

/-! Kernel checks of segments 2005-2008 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2005 : check start2005 proof2005 = true := by
  decide +kernel

theorem ok2006 : check start2006 proof2006 = true := by
  decide +kernel

theorem ok2007 : check start2007 proof2007 = true := by
  decide +kernel

theorem ok2008 : andB (check start2008 proof2008) (cpOk (replay start2008 proof2008) start2009) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
