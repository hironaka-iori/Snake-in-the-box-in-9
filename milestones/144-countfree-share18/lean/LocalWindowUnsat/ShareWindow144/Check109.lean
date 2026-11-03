import LocalWindowUnsat.ShareWindow144.Data109
import LocalWindowUnsat.ShareWindow144.Data110

/-! Kernel checks of segments 433-436 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok433 : check start433 proof433 = true := by
  decide +kernel

theorem ok434 : check start434 proof434 = true := by
  decide +kernel

theorem ok435 : check start435 proof435 = true := by
  decide +kernel

theorem ok436 : andB (check start436 proof436) (cpOk (replay start436 proof436) start437) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
