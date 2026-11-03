import Recovered122G.LocalWindowUnsat.End44.Data89
import Recovered122G.LocalWindowUnsat.End44.Data90

/-! Kernel checks of segments 529-534 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok529 : check start529 proof529 = true := by
  decide +kernel

theorem ok530 : check start530 proof530 = true := by
  decide +kernel

theorem ok531 : check start531 proof531 = true := by
  decide +kernel

theorem ok532 : check start532 proof532 = true := by
  decide +kernel

theorem ok533 : check start533 proof533 = true := by
  decide +kernel

theorem ok534 : andB (check start534 proof534) (cpOk (replay start534 proof534) start535) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
