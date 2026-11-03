import LocalWindowUnsat.ShareWindow144.Data17
import LocalWindowUnsat.ShareWindow144.Data18

/-! Kernel checks of segments 65-68 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok65 : check start65 proof65 = true := by
  decide +kernel

theorem ok66 : check start66 proof66 = true := by
  decide +kernel

theorem ok67 : check start67 proof67 = true := by
  decide +kernel

theorem ok68 : andB (check start68 proof68) (cpOk (replay start68 proof68) start69) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
