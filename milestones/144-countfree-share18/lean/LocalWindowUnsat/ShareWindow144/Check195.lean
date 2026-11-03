import LocalWindowUnsat.ShareWindow144.Data195
import LocalWindowUnsat.ShareWindow144.Data196

/-! Kernel checks of segments 777-780 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok777 : check start777 proof777 = true := by
  decide +kernel

theorem ok778 : check start778 proof778 = true := by
  decide +kernel

theorem ok779 : check start779 proof779 = true := by
  decide +kernel

theorem ok780 : andB (check start780 proof780) (cpOk (replay start780 proof780) start781) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
