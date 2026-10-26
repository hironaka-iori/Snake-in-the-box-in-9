import LocalWindowUnsat.SharePressure520.Data12
import LocalWindowUnsat.SharePressure520.Data13

/-! Kernel checks of segments 13-13 of `supported0_95` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SharePressure520
open Snake9.LratFastO6k14
open Snake9.LratO6k (Tree TreeTrue andB)

theorem ok13 : andB (check start13 proof13) (hasEmpty (replay start13 proof13) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.SharePressure520
