import LocalWindowUnsat.ShareWindow144.Data183
import LocalWindowUnsat.ShareWindow144.Data184

/-! Kernel checks of segments 729-732 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok729 : check start729 proof729 = true := by
  decide +kernel

theorem ok730 : check start730 proof730 = true := by
  decide +kernel

theorem ok731 : check start731 proof731 = true := by
  decide +kernel

theorem ok732 : andB (check start732 proof732) (cpOk (replay start732 proof732) start733) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
