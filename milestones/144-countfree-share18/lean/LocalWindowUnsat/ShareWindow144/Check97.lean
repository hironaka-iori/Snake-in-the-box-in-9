import LocalWindowUnsat.ShareWindow144.Data97
import LocalWindowUnsat.ShareWindow144.Data98

/-! Kernel checks of segments 385-388 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok385 : check start385 proof385 = true := by
  decide +kernel

theorem ok386 : check start386 proof386 = true := by
  decide +kernel

theorem ok387 : check start387 proof387 = true := by
  decide +kernel

theorem ok388 : andB (check start388 proof388) (cpOk (replay start388 proof388) start389) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
