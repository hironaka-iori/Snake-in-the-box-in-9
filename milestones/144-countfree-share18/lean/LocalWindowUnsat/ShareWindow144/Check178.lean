import LocalWindowUnsat.ShareWindow144.Data178
import LocalWindowUnsat.ShareWindow144.Data179

/-! Kernel checks of segments 709-712 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok709 : check start709 proof709 = true := by
  decide +kernel

theorem ok710 : check start710 proof710 = true := by
  decide +kernel

theorem ok711 : check start711 proof711 = true := by
  decide +kernel

theorem ok712 : andB (check start712 proof712) (cpOk (replay start712 proof712) start713) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
