import LocalWindowUnsat.ShareWindow144.Data504
import LocalWindowUnsat.ShareWindow144.Data505

/-! Kernel checks of segments 2013-2016 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2013 : check start2013 proof2013 = true := by
  decide +kernel

theorem ok2014 : check start2014 proof2014 = true := by
  decide +kernel

theorem ok2015 : check start2015 proof2015 = true := by
  decide +kernel

theorem ok2016 : andB (check start2016 proof2016) (cpOk (replay start2016 proof2016) start2017) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
