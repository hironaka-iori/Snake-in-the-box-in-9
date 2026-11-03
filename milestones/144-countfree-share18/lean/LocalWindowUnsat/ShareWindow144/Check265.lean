import LocalWindowUnsat.ShareWindow144.Data265
import LocalWindowUnsat.ShareWindow144.Data266

/-! Kernel checks of segments 1057-1060 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1057 : check start1057 proof1057 = true := by
  decide +kernel

theorem ok1058 : check start1058 proof1058 = true := by
  decide +kernel

theorem ok1059 : check start1059 proof1059 = true := by
  decide +kernel

theorem ok1060 : andB (check start1060 proof1060) (cpOk (replay start1060 proof1060) start1061) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
