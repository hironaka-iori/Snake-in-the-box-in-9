import LocalWindowUnsat.Middle325R.Data17
import LocalWindowUnsat.Middle325R.Data18

/-! Kernel checks of segments 65-68 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok65 : check start65 proof65 = true := by
  decide +kernel

theorem ok66 : check start66 proof66 = true := by
  decide +kernel

theorem ok67 : check start67 proof67 = true := by
  decide +kernel

theorem ok68 : andB (check start68 proof68) (cpOk (replay start68 proof68) start69) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
