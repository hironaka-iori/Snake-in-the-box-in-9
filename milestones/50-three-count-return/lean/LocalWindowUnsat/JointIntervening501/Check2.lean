import LocalWindowUnsat.JointIntervening501.Data6
import LocalWindowUnsat.JointIntervening501.Data7
import LocalWindowUnsat.JointIntervening501.Data8
import LocalWindowUnsat.JointIntervening501.Data9
import LocalWindowUnsat.JointIntervening501.Data10
import LocalWindowUnsat.JointIntervening501.Data11
import LocalWindowUnsat.JointIntervening501.Data12

/-! Kernel checks of segments 7-12 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok7 : check start7 proof7 = true := by
  decide +kernel

theorem ok8 : andB (check start8 proof8) (cpOk (replay start8 proof8) start9) = true := by
  decide +kernel

theorem ok9 : check start9 proof9 = true := by
  decide +kernel

theorem ok10 : check start10 proof10 = true := by
  decide +kernel

theorem ok11 : check start11 proof11 = true := by
  decide +kernel

theorem ok12 : andB (check start12 proof12) (cpOk (replay start12 proof12) start13) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
