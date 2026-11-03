import LocalWindowUnsat.ShareWindow144.Data102
import LocalWindowUnsat.ShareWindow144.Data103

/-! Kernel checks of segments 405-408 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok405 : check start405 proof405 = true := by
  decide +kernel

theorem ok406 : check start406 proof406 = true := by
  decide +kernel

theorem ok407 : check start407 proof407 = true := by
  decide +kernel

theorem ok408 : andB (check start408 proof408) (cpOk (replay start408 proof408) start409) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
