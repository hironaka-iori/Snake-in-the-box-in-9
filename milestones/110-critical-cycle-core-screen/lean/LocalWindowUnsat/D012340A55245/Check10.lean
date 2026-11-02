import LocalWindowUnsat.D012340A55245.Data9
import LocalWindowUnsat.D012340A55245.Data10

/-! Kernel checks of segments 10-10 of `d012340_a5_5_2_4_5` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.D012340A55245
open Snake9.LratFastO4k14
open Snake9.LratO4k (Tree TreeTrue andB)

theorem ok10 : andB (check start10 proof10) (cpOk (replay start10 proof10) start11) = true := by
  decide +kernel

end Snake9.LocalWindow.D012340A55245
