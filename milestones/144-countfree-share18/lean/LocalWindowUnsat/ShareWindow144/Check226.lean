import LocalWindowUnsat.ShareWindow144.Data226
import LocalWindowUnsat.ShareWindow144.Data227

/-! Kernel checks of segments 901-904 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok901 : check start901 proof901 = true := by
  decide +kernel

theorem ok902 : check start902 proof902 = true := by
  decide +kernel

theorem ok903 : check start903 proof903 = true := by
  decide +kernel

theorem ok904 : andB (check start904 proof904) (cpOk (replay start904 proof904) start905) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
