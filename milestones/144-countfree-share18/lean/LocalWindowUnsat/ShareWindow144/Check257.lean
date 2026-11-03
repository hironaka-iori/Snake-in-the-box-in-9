import LocalWindowUnsat.ShareWindow144.Data257
import LocalWindowUnsat.ShareWindow144.Data258

/-! Kernel checks of segments 1025-1028 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1025 : check start1025 proof1025 = true := by
  decide +kernel

theorem ok1026 : check start1026 proof1026 = true := by
  decide +kernel

theorem ok1027 : check start1027 proof1027 = true := by
  decide +kernel

theorem ok1028 : andB (check start1028 proof1028) (cpOk (replay start1028 proof1028) start1029) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
