import Recovered121G.LocalWindowUnsat.Lower032.Data8

/-! Kernel checks of segments 43-46 of `lower032` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Lower032
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok43 : check start43 proof43 = true := by
  decide +kernel

theorem ok44 : check start44 proof44 = true := by
  decide +kernel

theorem ok45 : check start45 proof45 = true := by
  decide +kernel

theorem ok46 : andB (check start46 proof46) (hasEmpty (replay start46 proof46) 512) = true := by
  decide +kernel

end Snake9.LocalWindow.Lower032
