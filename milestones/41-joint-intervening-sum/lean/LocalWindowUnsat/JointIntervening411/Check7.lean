import LocalWindowUnsat.JointIntervening411.Data36
import LocalWindowUnsat.JointIntervening411.Data37
import LocalWindowUnsat.JointIntervening411.Data38
import LocalWindowUnsat.JointIntervening411.Data39
import LocalWindowUnsat.JointIntervening411.Data40
import LocalWindowUnsat.JointIntervening411.Data41
import LocalWindowUnsat.JointIntervening411.Data42

/-! Kernel checks of segments 37-42 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : check start38 proof38 = true := by
  decide +kernel

theorem ok39 : check start39 proof39 = true := by
  decide +kernel

theorem ok40 : andB (check start40 proof40) (cpOk (replay start40 proof40) start41) = true := by
  decide +kernel

theorem ok41 : check start41 proof41 = true := by
  decide +kernel

theorem ok42 : check start42 proof42 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
