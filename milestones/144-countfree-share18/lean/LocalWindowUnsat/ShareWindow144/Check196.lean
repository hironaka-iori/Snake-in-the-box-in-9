import LocalWindowUnsat.ShareWindow144.Data196
import LocalWindowUnsat.ShareWindow144.Data197

/-! Kernel checks of segments 781-784 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok781 : check start781 proof781 = true := by
  decide +kernel

theorem ok782 : check start782 proof782 = true := by
  decide +kernel

theorem ok783 : check start783 proof783 = true := by
  decide +kernel

theorem ok784 : andB (check start784 proof784) (cpOk (replay start784 proof784) start785) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
