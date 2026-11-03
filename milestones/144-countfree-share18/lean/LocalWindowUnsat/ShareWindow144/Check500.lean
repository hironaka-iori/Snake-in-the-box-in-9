import LocalWindowUnsat.ShareWindow144.Data500
import LocalWindowUnsat.ShareWindow144.Data501

/-! Kernel checks of segments 1997-2000 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1997 : check start1997 proof1997 = true := by
  decide +kernel

theorem ok1998 : check start1998 proof1998 = true := by
  decide +kernel

theorem ok1999 : check start1999 proof1999 = true := by
  decide +kernel

theorem ok2000 : andB (check start2000 proof2000) (cpOk (replay start2000 proof2000) start2001) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
