import LocalWindowUnsat.ShareWindow144.Data225
import LocalWindowUnsat.ShareWindow144.Data226

/-! Kernel checks of segments 897-900 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok897 : check start897 proof897 = true := by
  decide +kernel

theorem ok898 : check start898 proof898 = true := by
  decide +kernel

theorem ok899 : check start899 proof899 = true := by
  decide +kernel

theorem ok900 : andB (check start900 proof900) (cpOk (replay start900 proof900) start901) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
