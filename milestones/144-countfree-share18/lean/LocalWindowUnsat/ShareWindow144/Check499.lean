import LocalWindowUnsat.ShareWindow144.Data499
import LocalWindowUnsat.ShareWindow144.Data500

/-! Kernel checks of segments 1993-1996 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1993 : check start1993 proof1993 = true := by
  decide +kernel

theorem ok1994 : check start1994 proof1994 = true := by
  decide +kernel

theorem ok1995 : check start1995 proof1995 = true := by
  decide +kernel

theorem ok1996 : andB (check start1996 proof1996) (cpOk (replay start1996 proof1996) start1997) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
