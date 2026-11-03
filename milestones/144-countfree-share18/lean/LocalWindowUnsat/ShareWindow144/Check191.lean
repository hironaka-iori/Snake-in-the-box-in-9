import LocalWindowUnsat.ShareWindow144.Data191
import LocalWindowUnsat.ShareWindow144.Data192

/-! Kernel checks of segments 761-764 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok761 : check start761 proof761 = true := by
  decide +kernel

theorem ok762 : check start762 proof762 = true := by
  decide +kernel

theorem ok763 : check start763 proof763 = true := by
  decide +kernel

theorem ok764 : andB (check start764 proof764) (cpOk (replay start764 proof764) start765) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
