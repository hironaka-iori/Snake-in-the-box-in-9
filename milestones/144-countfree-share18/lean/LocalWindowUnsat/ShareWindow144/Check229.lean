import LocalWindowUnsat.ShareWindow144.Data229
import LocalWindowUnsat.ShareWindow144.Data230

/-! Kernel checks of segments 913-916 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok913 : check start913 proof913 = true := by
  decide +kernel

theorem ok914 : check start914 proof914 = true := by
  decide +kernel

theorem ok915 : check start915 proof915 = true := by
  decide +kernel

theorem ok916 : andB (check start916 proof916) (cpOk (replay start916 proof916) start917) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
