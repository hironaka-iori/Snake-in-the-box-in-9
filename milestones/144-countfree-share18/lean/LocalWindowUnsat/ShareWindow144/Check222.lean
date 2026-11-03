import LocalWindowUnsat.ShareWindow144.Data222
import LocalWindowUnsat.ShareWindow144.Data223

/-! Kernel checks of segments 885-888 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok885 : check start885 proof885 = true := by
  decide +kernel

theorem ok886 : check start886 proof886 = true := by
  decide +kernel

theorem ok887 : check start887 proof887 = true := by
  decide +kernel

theorem ok888 : andB (check start888 proof888) (cpOk (replay start888 proof888) start889) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
