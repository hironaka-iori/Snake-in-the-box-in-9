import LocalWindowUnsat.ShareWindow144.Data247
import LocalWindowUnsat.ShareWindow144.Data248

/-! Kernel checks of segments 985-988 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok985 : check start985 proof985 = true := by
  decide +kernel

theorem ok986 : check start986 proof986 = true := by
  decide +kernel

theorem ok987 : check start987 proof987 = true := by
  decide +kernel

theorem ok988 : andB (check start988 proof988) (cpOk (replay start988 proof988) start989) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
