import LocalWindowUnsat.ShareWindow144.Data170
import LocalWindowUnsat.ShareWindow144.Data171

/-! Kernel checks of segments 677-680 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok677 : check start677 proof677 = true := by
  decide +kernel

theorem ok678 : check start678 proof678 = true := by
  decide +kernel

theorem ok679 : check start679 proof679 = true := by
  decide +kernel

theorem ok680 : andB (check start680 proof680) (cpOk (replay start680 proof680) start681) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
