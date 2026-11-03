import LocalWindowUnsat.ShareWindow144.Data501
import LocalWindowUnsat.ShareWindow144.Data502

/-! Kernel checks of segments 2001-2004 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2001 : check start2001 proof2001 = true := by
  decide +kernel

theorem ok2002 : check start2002 proof2002 = true := by
  decide +kernel

theorem ok2003 : check start2003 proof2003 = true := by
  decide +kernel

theorem ok2004 : andB (check start2004 proof2004) (cpOk (replay start2004 proof2004) start2005) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
