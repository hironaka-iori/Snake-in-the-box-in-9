import Recovered122G.LocalWindowUnsat.End44.Data84
import Recovered122G.LocalWindowUnsat.End44.Data85

/-! Kernel checks of segments 499-504 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok499 : check start499 proof499 = true := by
  decide +kernel

theorem ok500 : check start500 proof500 = true := by
  decide +kernel

theorem ok501 : check start501 proof501 = true := by
  decide +kernel

theorem ok502 : check start502 proof502 = true := by
  decide +kernel

theorem ok503 : check start503 proof503 = true := by
  decide +kernel

theorem ok504 : andB (check start504 proof504) (cpOk (replay start504 proof504) start505) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
