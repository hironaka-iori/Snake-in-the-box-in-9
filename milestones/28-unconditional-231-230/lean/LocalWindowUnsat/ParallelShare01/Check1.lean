import LocalWindowUnsat.ParallelShare01.Data1

/-! Kernel checks of segments 1-1 of `parallel_share_01` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ParallelShare01
open Snake9.LratFastP2400W17
open Snake9.LratFast2P2400W17
open Snake9.LratP2400 (Tree TreeTrue andB)

theorem ok1 : andB (check2 start1 (perf 7 0) proof1) (hasEmpty (replay start1 proof1) 64) = true := by
  decide +kernel

end Snake9.LocalWindow.ParallelShare01
