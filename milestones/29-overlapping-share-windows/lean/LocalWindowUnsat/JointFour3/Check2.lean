import LocalWindowUnsat.JointFour3.Data6
import LocalWindowUnsat.JointFour3.Data7
import LocalWindowUnsat.JointFour3.Data8
import LocalWindowUnsat.JointFour3.Data9
import LocalWindowUnsat.JointFour3.Data10
import LocalWindowUnsat.JointFour3.Data11

/-! Kernel checks of segments 7-11 of `joint3` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointFour3
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok7 : check start7 proof7 = true := by
  decide +kernel

theorem ok8 : andB (check start8 proof8) (cpOk (replay start8 proof8) start9) = true := by
  decide +kernel

theorem ok9 : check start9 proof9 = true := by
  decide +kernel

theorem ok10 : check start10 proof10 = true := by
  decide +kernel

theorem ok11 : andB (check start11 proof11) (hasEmpty (replay start11 proof11) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.JointFour3
