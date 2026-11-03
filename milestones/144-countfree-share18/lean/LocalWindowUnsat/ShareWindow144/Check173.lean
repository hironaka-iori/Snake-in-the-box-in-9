import LocalWindowUnsat.ShareWindow144.Data173
import LocalWindowUnsat.ShareWindow144.Data174

/-! Kernel checks of segments 689-692 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok689 : check start689 proof689 = true := by
  decide +kernel

theorem ok690 : check start690 proof690 = true := by
  decide +kernel

theorem ok691 : check start691 proof691 = true := by
  decide +kernel

theorem ok692 : andB (check start692 proof692) (cpOk (replay start692 proof692) start693) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
