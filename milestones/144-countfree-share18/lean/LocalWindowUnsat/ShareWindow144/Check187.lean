import LocalWindowUnsat.ShareWindow144.Data187
import LocalWindowUnsat.ShareWindow144.Data188

/-! Kernel checks of segments 745-748 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok745 : check start745 proof745 = true := by
  decide +kernel

theorem ok746 : check start746 proof746 = true := by
  decide +kernel

theorem ok747 : check start747 proof747 = true := by
  decide +kernel

theorem ok748 : andB (check start748 proof748) (cpOk (replay start748 proof748) start749) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
