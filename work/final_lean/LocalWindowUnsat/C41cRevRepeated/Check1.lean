import LocalWindowUnsat.C41cRevRepeated.Data1

/-! Kernel checks of segments 1-1 of `41c_rev_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C41cRevRepeated
open Snake9.Lrat

theorem ok1 : andB (check start1 proof1) (hasEmpty (replay start1 proof1) 166) = true := by
  decide +kernel

end Snake9.LocalWindow.C41cRevRepeated
