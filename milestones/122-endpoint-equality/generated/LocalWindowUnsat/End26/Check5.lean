import LocalWindowUnsat.End26.Data5
import LocalWindowUnsat.End26.Data6

/-! Kernel checks of segments 25-30 of `end26` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End26
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok25 : check start25 proof25 = true := by
  decide +kernel

theorem ok26 : check start26 proof26 = true := by
  decide +kernel

theorem ok27 : check start27 proof27 = true := by
  decide +kernel

theorem ok28 : check start28 proof28 = true := by
  decide +kernel

theorem ok29 : check start29 proof29 = true := by
  decide +kernel

theorem ok30 : andB (check start30 proof30) (cpOk (replay start30 proof30) start31) = true := by
  decide +kernel

end Snake9.LocalWindow.End26
