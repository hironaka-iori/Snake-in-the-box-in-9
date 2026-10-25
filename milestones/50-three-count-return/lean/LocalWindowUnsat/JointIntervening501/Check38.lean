import LocalWindowUnsat.JointIntervening501.Data222
import LocalWindowUnsat.JointIntervening501.Data223
import LocalWindowUnsat.JointIntervening501.Data224
import LocalWindowUnsat.JointIntervening501.Data225
import LocalWindowUnsat.JointIntervening501.Data226
import LocalWindowUnsat.JointIntervening501.Data227
import LocalWindowUnsat.JointIntervening501.Data228

/-! Kernel checks of segments 223-228 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok223 : check start223 proof223 = true := by
  decide +kernel

theorem ok224 : andB (check start224 proof224) (cpOk (replay start224 proof224) start225) = true := by
  decide +kernel

theorem ok225 : check start225 proof225 = true := by
  decide +kernel

theorem ok226 : check start226 proof226 = true := by
  decide +kernel

theorem ok227 : check start227 proof227 = true := by
  decide +kernel

theorem ok228 : andB (check start228 proof228) (cpOk (replay start228 proof228) start229) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
