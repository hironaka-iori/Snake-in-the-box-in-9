import LocalWindowUnsat.CycleWindow4903.Data24
import LocalWindowUnsat.CycleWindow4903.Data25
import LocalWindowUnsat.CycleWindow4903.Data26
import LocalWindowUnsat.CycleWindow4903.Data27
import LocalWindowUnsat.CycleWindow4903.Data28
import LocalWindowUnsat.CycleWindow4903.Data29

/-! Kernel checks of segments 25-29 of `cycle4903` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4903
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok25 : check start25 proof25 = true := by
  decide +kernel

theorem ok26 : check start26 proof26 = true := by
  decide +kernel

theorem ok27 : check start27 proof27 = true := by
  decide +kernel

theorem ok28 : andB (check start28 proof28) (cpOk (replay start28 proof28) start29) = true := by
  decide +kernel

theorem ok29 : andB (check start29 proof29) (hasEmpty (replay start29 proof29) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4903
