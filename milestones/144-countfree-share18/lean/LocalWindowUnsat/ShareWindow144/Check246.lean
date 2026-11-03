import LocalWindowUnsat.ShareWindow144.Data246
import LocalWindowUnsat.ShareWindow144.Data247

/-! Kernel checks of segments 981-984 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok981 : check start981 proof981 = true := by
  decide +kernel

theorem ok982 : check start982 proof982 = true := by
  decide +kernel

theorem ok983 : check start983 proof983 = true := by
  decide +kernel

theorem ok984 : andB (check start984 proof984) (cpOk (replay start984 proof984) start985) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
