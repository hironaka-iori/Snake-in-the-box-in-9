import LocalWindowUnsat.ShareWindow144.Data181
import LocalWindowUnsat.ShareWindow144.Data182

/-! Kernel checks of segments 721-724 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok721 : check start721 proof721 = true := by
  decide +kernel

theorem ok722 : check start722 proof722 = true := by
  decide +kernel

theorem ok723 : check start723 proof723 = true := by
  decide +kernel

theorem ok724 : andB (check start724 proof724) (cpOk (replay start724 proof724) start725) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
