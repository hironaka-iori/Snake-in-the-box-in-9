import LocalWindowUnsat.ShareWindow144.Data147
import LocalWindowUnsat.ShareWindow144.Data148

/-! Kernel checks of segments 585-588 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok585 : check start585 proof585 = true := by
  decide +kernel

theorem ok586 : check start586 proof586 = true := by
  decide +kernel

theorem ok587 : check start587 proof587 = true := by
  decide +kernel

theorem ok588 : andB (check start588 proof588) (cpOk (replay start588 proof588) start589) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
