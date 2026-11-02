import Recovered110.LocalWindowUnsat.D012340A55245.Data14
import Recovered110.LocalWindowUnsat.D012340A55245.Data15

/-! Kernel checks of segments 15-15 of `d012340_a5_5_2_4_5` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.D012340A55245
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok15 : check start15 proof15 = true := by
  decide +kernel

end Snake9.LocalWindow.D012340A55245
