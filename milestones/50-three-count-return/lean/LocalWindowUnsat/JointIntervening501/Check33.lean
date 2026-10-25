import LocalWindowUnsat.JointIntervening501.Data192
import LocalWindowUnsat.JointIntervening501.Data193
import LocalWindowUnsat.JointIntervening501.Data194
import LocalWindowUnsat.JointIntervening501.Data195
import LocalWindowUnsat.JointIntervening501.Data196
import LocalWindowUnsat.JointIntervening501.Data197
import LocalWindowUnsat.JointIntervening501.Data198

/-! Kernel checks of segments 193-198 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok193 : check start193 proof193 = true := by
  decide +kernel

theorem ok194 : check start194 proof194 = true := by
  decide +kernel

theorem ok195 : check start195 proof195 = true := by
  decide +kernel

theorem ok196 : andB (check start196 proof196) (cpOk (replay start196 proof196) start197) = true := by
  decide +kernel

theorem ok197 : check start197 proof197 = true := by
  decide +kernel

theorem ok198 : check start198 proof198 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
