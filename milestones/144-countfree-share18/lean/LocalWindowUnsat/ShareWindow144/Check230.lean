import LocalWindowUnsat.ShareWindow144.Data230
import LocalWindowUnsat.ShareWindow144.Data231

/-! Kernel checks of segments 917-920 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok917 : check start917 proof917 = true := by
  decide +kernel

theorem ok918 : check start918 proof918 = true := by
  decide +kernel

theorem ok919 : check start919 proof919 = true := by
  decide +kernel

theorem ok920 : andB (check start920 proof920) (cpOk (replay start920 proof920) start921) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
