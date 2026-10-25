import LocalWindowUnsat.JointIntervening501.Data210
import LocalWindowUnsat.JointIntervening501.Data211
import LocalWindowUnsat.JointIntervening501.Data212
import LocalWindowUnsat.JointIntervening501.Data213
import LocalWindowUnsat.JointIntervening501.Data214
import LocalWindowUnsat.JointIntervening501.Data215
import LocalWindowUnsat.JointIntervening501.Data216

/-! Kernel checks of segments 211-216 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok211 : check start211 proof211 = true := by
  decide +kernel

theorem ok212 : andB (check start212 proof212) (cpOk (replay start212 proof212) start213) = true := by
  decide +kernel

theorem ok213 : check start213 proof213 = true := by
  decide +kernel

theorem ok214 : check start214 proof214 = true := by
  decide +kernel

theorem ok215 : check start215 proof215 = true := by
  decide +kernel

theorem ok216 : andB (check start216 proof216) (cpOk (replay start216 proof216) start217) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
