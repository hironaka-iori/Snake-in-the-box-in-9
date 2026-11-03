import LocalWindowUnsat.ShareWindow144.Data215
import LocalWindowUnsat.ShareWindow144.Data216

/-! Kernel checks of segments 857-860 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok857 : check start857 proof857 = true := by
  decide +kernel

theorem ok858 : check start858 proof858 = true := by
  decide +kernel

theorem ok859 : check start859 proof859 = true := by
  decide +kernel

theorem ok860 : andB (check start860 proof860) (cpOk (replay start860 proof860) start861) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
