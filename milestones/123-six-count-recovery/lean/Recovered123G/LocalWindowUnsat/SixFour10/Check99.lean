import Recovered123G.LocalWindowUnsat.SixFour10.Data99

/-! Kernel checks of segments 589-590 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok589 : check start589 proof589 = true := by
  decide +kernel

theorem ok590 : andB (check start590 proof590) (hasEmpty (replay start590 proof590) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
