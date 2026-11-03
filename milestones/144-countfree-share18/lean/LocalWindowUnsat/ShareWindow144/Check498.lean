import LocalWindowUnsat.ShareWindow144.Data498
import LocalWindowUnsat.ShareWindow144.Data499

/-! Kernel checks of segments 1989-1992 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1989 : check start1989 proof1989 = true := by
  decide +kernel

theorem ok1990 : check start1990 proof1990 = true := by
  decide +kernel

theorem ok1991 : check start1991 proof1991 = true := by
  decide +kernel

theorem ok1992 : andB (check start1992 proof1992) (cpOk (replay start1992 proof1992) start1993) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
