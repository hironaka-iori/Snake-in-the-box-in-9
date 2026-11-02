import LocalWindowUnsat.D012340A55245.Data63
import LocalWindowUnsat.D012340A55245.Data64

/-! Kernel checks of segments 64-64 of `d012340_a5_5_2_4_5` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.D012340A55245
open Snake9.LratFastO4k14
open Snake9.LratO4k (Tree TreeTrue andB)

theorem ok64 : andB (check start64 proof64) (cpOk (replay start64 proof64) start65) = true := by
  decide +kernel

end Snake9.LocalWindow.D012340A55245
