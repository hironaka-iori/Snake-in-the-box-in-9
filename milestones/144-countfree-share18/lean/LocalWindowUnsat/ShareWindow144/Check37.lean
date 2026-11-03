import LocalWindowUnsat.ShareWindow144.Data37
import LocalWindowUnsat.ShareWindow144.Data38

/-! Kernel checks of segments 145-148 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok145 : check start145 proof145 = true := by
  decide +kernel

theorem ok146 : check start146 proof146 = true := by
  decide +kernel

theorem ok147 : check start147 proof147 = true := by
  decide +kernel

theorem ok148 : andB (check start148 proof148) (cpOk (replay start148 proof148) start149) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
