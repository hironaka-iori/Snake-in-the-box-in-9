import Recovered122G.LocalWindowUnsat.End35.Data62
import Recovered122G.LocalWindowUnsat.End35.Data63

/-! Kernel checks of segments 367-372 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok367 : check start367 proof367 = true := by
  decide +kernel

theorem ok368 : check start368 proof368 = true := by
  decide +kernel

theorem ok369 : check start369 proof369 = true := by
  decide +kernel

theorem ok370 : check start370 proof370 = true := by
  decide +kernel

theorem ok371 : check start371 proof371 = true := by
  decide +kernel

theorem ok372 : andB (check start372 proof372) (cpOk (replay start372 proof372) start373) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
