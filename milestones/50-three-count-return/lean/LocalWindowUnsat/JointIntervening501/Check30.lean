import LocalWindowUnsat.JointIntervening501.Data174
import LocalWindowUnsat.JointIntervening501.Data175
import LocalWindowUnsat.JointIntervening501.Data176
import LocalWindowUnsat.JointIntervening501.Data177
import LocalWindowUnsat.JointIntervening501.Data178
import LocalWindowUnsat.JointIntervening501.Data179
import LocalWindowUnsat.JointIntervening501.Data180

/-! Kernel checks of segments 175-180 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok175 : check start175 proof175 = true := by
  decide +kernel

theorem ok176 : andB (check start176 proof176) (cpOk (replay start176 proof176) start177) = true := by
  decide +kernel

theorem ok177 : check start177 proof177 = true := by
  decide +kernel

theorem ok178 : check start178 proof178 = true := by
  decide +kernel

theorem ok179 : check start179 proof179 = true := by
  decide +kernel

theorem ok180 : andB (check start180 proof180) (cpOk (replay start180 proof180) start181) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
