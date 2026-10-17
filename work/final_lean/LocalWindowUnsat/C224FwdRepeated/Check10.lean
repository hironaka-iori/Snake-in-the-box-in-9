import LocalWindowUnsat.C224FwdRepeated.Data40

/-! Kernel checks of segments 37-40 of `224_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C224FwdRepeated
open Snake9.Lrat

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : check start38 proof38 = true := by
  decide +kernel

theorem ok39 : andB (check start39 proof39) (cpOk (replay start39 proof39) cp40) = true := by
  decide +kernel

theorem ok40 : andB (check start40 proof40) (hasEmpty (replay start40 proof40) 1024) = true := by
  decide +kernel

end Snake9.LocalWindow.C224FwdRepeated
