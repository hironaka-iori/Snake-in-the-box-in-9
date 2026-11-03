import LocalWindowUnsat.Lower032.Data7
import LocalWindowUnsat.Lower032.Data8

/-! Kernel checks of segments 37-42 of `lower032` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Lower032
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : check start38 proof38 = true := by
  decide +kernel

theorem ok39 : check start39 proof39 = true := by
  decide +kernel

theorem ok40 : check start40 proof40 = true := by
  decide +kernel

theorem ok41 : check start41 proof41 = true := by
  decide +kernel

theorem ok42 : andB (check start42 proof42) (cpOk (replay start42 proof42) start43) = true := by
  decide +kernel

end Snake9.LocalWindow.Lower032
