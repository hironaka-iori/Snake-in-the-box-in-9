import LocalWindowUnsat.JointIntervening501.Data186
import LocalWindowUnsat.JointIntervening501.Data187
import LocalWindowUnsat.JointIntervening501.Data188
import LocalWindowUnsat.JointIntervening501.Data189
import LocalWindowUnsat.JointIntervening501.Data190
import LocalWindowUnsat.JointIntervening501.Data191
import LocalWindowUnsat.JointIntervening501.Data192

/-! Kernel checks of segments 187-192 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok187 : check start187 proof187 = true := by
  decide +kernel

theorem ok188 : andB (check start188 proof188) (cpOk (replay start188 proof188) start189) = true := by
  decide +kernel

theorem ok189 : check start189 proof189 = true := by
  decide +kernel

theorem ok190 : check start190 proof190 = true := by
  decide +kernel

theorem ok191 : check start191 proof191 = true := by
  decide +kernel

theorem ok192 : andB (check start192 proof192) (cpOk (replay start192 proof192) start193) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
