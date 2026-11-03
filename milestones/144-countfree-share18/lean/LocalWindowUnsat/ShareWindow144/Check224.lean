import LocalWindowUnsat.ShareWindow144.Data224
import LocalWindowUnsat.ShareWindow144.Data225

/-! Kernel checks of segments 893-896 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok893 : check start893 proof893 = true := by
  decide +kernel

theorem ok894 : check start894 proof894 = true := by
  decide +kernel

theorem ok895 : check start895 proof895 = true := by
  decide +kernel

theorem ok896 : andB (check start896 proof896) (cpOk (replay start896 proof896) start897) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
