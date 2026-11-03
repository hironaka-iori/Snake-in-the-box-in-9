import LocalWindowUnsat.ShareWindow144.Data171
import LocalWindowUnsat.ShareWindow144.Data172

/-! Kernel checks of segments 681-684 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok681 : check start681 proof681 = true := by
  decide +kernel

theorem ok682 : check start682 proof682 = true := by
  decide +kernel

theorem ok683 : check start683 proof683 = true := by
  decide +kernel

theorem ok684 : andB (check start684 proof684) (cpOk (replay start684 proof684) start685) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
