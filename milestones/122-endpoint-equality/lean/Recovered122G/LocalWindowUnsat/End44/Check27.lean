import Recovered122G.LocalWindowUnsat.End44.Data27
import Recovered122G.LocalWindowUnsat.End44.Data28

/-! Kernel checks of segments 157-162 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok157 : check start157 proof157 = true := by
  decide +kernel

theorem ok158 : check start158 proof158 = true := by
  decide +kernel

theorem ok159 : check start159 proof159 = true := by
  decide +kernel

theorem ok160 : check start160 proof160 = true := by
  decide +kernel

theorem ok161 : check start161 proof161 = true := by
  decide +kernel

theorem ok162 : andB (check start162 proof162) (cpOk (replay start162 proof162) start163) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
