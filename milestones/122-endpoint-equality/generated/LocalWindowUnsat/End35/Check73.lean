import LocalWindowUnsat.End35.Data73
import LocalWindowUnsat.End35.Data74

/-! Kernel checks of segments 433-438 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok433 : check start433 proof433 = true := by
  decide +kernel

theorem ok434 : check start434 proof434 = true := by
  decide +kernel

theorem ok435 : check start435 proof435 = true := by
  decide +kernel

theorem ok436 : check start436 proof436 = true := by
  decide +kernel

theorem ok437 : check start437 proof437 = true := by
  decide +kernel

theorem ok438 : andB (check start438 proof438) (cpOk (replay start438 proof438) start439) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
