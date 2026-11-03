import LocalWindowUnsat.ShareWindow144.Data460
import LocalWindowUnsat.ShareWindow144.Data461

/-! Kernel checks of segments 1837-1840 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1837 : check start1837 proof1837 = true := by
  decide +kernel

theorem ok1838 : check start1838 proof1838 = true := by
  decide +kernel

theorem ok1839 : check start1839 proof1839 = true := by
  decide +kernel

theorem ok1840 : andB (check start1840 proof1840) (cpOk (replay start1840 proof1840) start1841) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
