import LocalWindowUnsat.ShareWindow144.Data32
import LocalWindowUnsat.ShareWindow144.Data33

/-! Kernel checks of segments 125-128 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok125 : check start125 proof125 = true := by
  decide +kernel

theorem ok126 : check start126 proof126 = true := by
  decide +kernel

theorem ok127 : check start127 proof127 = true := by
  decide +kernel

theorem ok128 : andB (check start128 proof128) (cpOk (replay start128 proof128) start129) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
