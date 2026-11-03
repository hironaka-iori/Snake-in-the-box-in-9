import Recovered122G.LocalWindowUnsat.End35.Data8
import Recovered122G.LocalWindowUnsat.End35.Data9

/-! Kernel checks of segments 43-48 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok43 : check start43 proof43 = true := by
  decide +kernel

theorem ok44 : check start44 proof44 = true := by
  decide +kernel

theorem ok45 : check start45 proof45 = true := by
  decide +kernel

theorem ok46 : check start46 proof46 = true := by
  decide +kernel

theorem ok47 : check start47 proof47 = true := by
  decide +kernel

theorem ok48 : andB (check start48 proof48) (cpOk (replay start48 proof48) start49) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
