import LocalWindowUnsat.ShareWindow144.Data85
import LocalWindowUnsat.ShareWindow144.Data86

/-! Kernel checks of segments 337-340 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok337 : check start337 proof337 = true := by
  decide +kernel

theorem ok338 : check start338 proof338 = true := by
  decide +kernel

theorem ok339 : check start339 proof339 = true := by
  decide +kernel

theorem ok340 : andB (check start340 proof340) (cpOk (replay start340 proof340) start341) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
