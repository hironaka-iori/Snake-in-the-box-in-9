import LocalWindowUnsat.ShareWindow144.Data272
import LocalWindowUnsat.ShareWindow144.Data273

/-! Kernel checks of segments 1085-1088 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1085 : check start1085 proof1085 = true := by
  decide +kernel

theorem ok1086 : check start1086 proof1086 = true := by
  decide +kernel

theorem ok1087 : check start1087 proof1087 = true := by
  decide +kernel

theorem ok1088 : andB (check start1088 proof1088) (cpOk (replay start1088 proof1088) start1089) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
