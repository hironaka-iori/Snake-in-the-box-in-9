import LocalWindowUnsat.Pair34032.Data8

/-! Kernel checks of segments 43-48 of `pair34032` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Pair34032
open Snake9.LratFast
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

theorem ok48 : andB (check start48 proof48) (hasEmpty (replay start48 proof48) 512) = true := by
  decide +kernel

end Snake9.LocalWindow.Pair34032
