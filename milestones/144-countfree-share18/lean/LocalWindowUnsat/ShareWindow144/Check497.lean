import LocalWindowUnsat.ShareWindow144.Data497
import LocalWindowUnsat.ShareWindow144.Data498

/-! Kernel checks of segments 1985-1988 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1985 : check start1985 proof1985 = true := by
  decide +kernel

theorem ok1986 : check start1986 proof1986 = true := by
  decide +kernel

theorem ok1987 : check start1987 proof1987 = true := by
  decide +kernel

theorem ok1988 : andB (check start1988 proof1988) (cpOk (replay start1988 proof1988) start1989) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
