import LocalWindowUnsat.ShareWindow144.Data433
import LocalWindowUnsat.ShareWindow144.Data434

/-! Kernel checks of segments 1729-1732 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1729 : check start1729 proof1729 = true := by
  decide +kernel

theorem ok1730 : check start1730 proof1730 = true := by
  decide +kernel

theorem ok1731 : check start1731 proof1731 = true := by
  decide +kernel

theorem ok1732 : andB (check start1732 proof1732) (cpOk (replay start1732 proof1732) start1733) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
