import LocalWindowUnsat.ShareWindow144.Data486
import LocalWindowUnsat.ShareWindow144.Data487

/-! Kernel checks of segments 1941-1944 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1941 : check start1941 proof1941 = true := by
  decide +kernel

theorem ok1942 : check start1942 proof1942 = true := by
  decide +kernel

theorem ok1943 : check start1943 proof1943 = true := by
  decide +kernel

theorem ok1944 : andB (check start1944 proof1944) (cpOk (replay start1944 proof1944) start1945) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
