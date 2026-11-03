import LocalWindowUnsat.ShareWindow144.Data197
import LocalWindowUnsat.ShareWindow144.Data198

/-! Kernel checks of segments 785-788 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok785 : check start785 proof785 = true := by
  decide +kernel

theorem ok786 : check start786 proof786 = true := by
  decide +kernel

theorem ok787 : check start787 proof787 = true := by
  decide +kernel

theorem ok788 : andB (check start788 proof788) (cpOk (replay start788 proof788) start789) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
