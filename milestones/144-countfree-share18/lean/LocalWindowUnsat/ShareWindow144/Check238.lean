import LocalWindowUnsat.ShareWindow144.Data238
import LocalWindowUnsat.ShareWindow144.Data239

/-! Kernel checks of segments 949-952 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok949 : check start949 proof949 = true := by
  decide +kernel

theorem ok950 : check start950 proof950 = true := by
  decide +kernel

theorem ok951 : check start951 proof951 = true := by
  decide +kernel

theorem ok952 : andB (check start952 proof952) (cpOk (replay start952 proof952) start953) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
