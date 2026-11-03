import LocalWindowUnsat.ShareWindow144.Data248
import LocalWindowUnsat.ShareWindow144.Data249

/-! Kernel checks of segments 989-992 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok989 : check start989 proof989 = true := by
  decide +kernel

theorem ok990 : check start990 proof990 = true := by
  decide +kernel

theorem ok991 : check start991 proof991 = true := by
  decide +kernel

theorem ok992 : andB (check start992 proof992) (cpOk (replay start992 proof992) start993) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
