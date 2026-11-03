import LocalWindowUnsat.ShareWindow144.Data43
import LocalWindowUnsat.ShareWindow144.Data44

/-! Kernel checks of segments 169-172 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok169 : check start169 proof169 = true := by
  decide +kernel

theorem ok170 : check start170 proof170 = true := by
  decide +kernel

theorem ok171 : check start171 proof171 = true := by
  decide +kernel

theorem ok172 : andB (check start172 proof172) (cpOk (replay start172 proof172) start173) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
