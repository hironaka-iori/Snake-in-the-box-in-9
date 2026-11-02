import LocalWindowUnsat.D012340A55245.Data41
import LocalWindowUnsat.D012340A55245.Data42

/-! Kernel checks of segments 42-42 of `d012340_a5_5_2_4_5` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.D012340A55245
open Snake9.LratFastO4k14
open Snake9.LratO4k (Tree TreeTrue andB)

theorem ok42 : andB (check start42 proof42) (cpOk (replay start42 proof42) start43) = true := by
  decide +kernel

end Snake9.LocalWindow.D012340A55245
