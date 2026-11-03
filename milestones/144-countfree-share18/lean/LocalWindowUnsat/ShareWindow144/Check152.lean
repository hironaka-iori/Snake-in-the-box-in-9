import LocalWindowUnsat.ShareWindow144.Data152
import LocalWindowUnsat.ShareWindow144.Data153

/-! Kernel checks of segments 605-608 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok605 : check start605 proof605 = true := by
  decide +kernel

theorem ok606 : check start606 proof606 = true := by
  decide +kernel

theorem ok607 : check start607 proof607 = true := by
  decide +kernel

theorem ok608 : andB (check start608 proof608) (cpOk (replay start608 proof608) start609) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
