import LocalWindowUnsat.D012340A55245.Data20
import LocalWindowUnsat.D012340A55245.Data21

/-! Kernel checks of segments 21-21 of `d012340_a5_5_2_4_5` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.D012340A55245
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok21 : check start21 proof21 = true := by
  decide +kernel

end Snake9.LocalWindow.D012340A55245
