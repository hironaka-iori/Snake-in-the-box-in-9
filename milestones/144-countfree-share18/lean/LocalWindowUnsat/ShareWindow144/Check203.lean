import LocalWindowUnsat.ShareWindow144.Data203
import LocalWindowUnsat.ShareWindow144.Data204

/-! Kernel checks of segments 809-812 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok809 : check start809 proof809 = true := by
  decide +kernel

theorem ok810 : check start810 proof810 = true := by
  decide +kernel

theorem ok811 : check start811 proof811 = true := by
  decide +kernel

theorem ok812 : andB (check start812 proof812) (cpOk (replay start812 proof812) start813) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
