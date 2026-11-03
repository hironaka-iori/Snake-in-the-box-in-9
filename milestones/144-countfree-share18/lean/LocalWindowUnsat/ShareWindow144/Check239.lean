import LocalWindowUnsat.ShareWindow144.Data239
import LocalWindowUnsat.ShareWindow144.Data240

/-! Kernel checks of segments 953-956 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok953 : check start953 proof953 = true := by
  decide +kernel

theorem ok954 : check start954 proof954 = true := by
  decide +kernel

theorem ok955 : check start955 proof955 = true := by
  decide +kernel

theorem ok956 : andB (check start956 proof956) (cpOk (replay start956 proof956) start957) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
