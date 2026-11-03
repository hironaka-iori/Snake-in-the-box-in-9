import LocalWindowUnsat.ShareWindow144.Data228
import LocalWindowUnsat.ShareWindow144.Data229

/-! Kernel checks of segments 909-912 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok909 : check start909 proof909 = true := by
  decide +kernel

theorem ok910 : check start910 proof910 = true := by
  decide +kernel

theorem ok911 : check start911 proof911 = true := by
  decide +kernel

theorem ok912 : andB (check start912 proof912) (cpOk (replay start912 proof912) start913) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
