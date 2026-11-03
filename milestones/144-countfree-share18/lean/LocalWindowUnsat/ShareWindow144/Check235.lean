import LocalWindowUnsat.ShareWindow144.Data235
import LocalWindowUnsat.ShareWindow144.Data236

/-! Kernel checks of segments 937-940 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok937 : check start937 proof937 = true := by
  decide +kernel

theorem ok938 : check start938 proof938 = true := by
  decide +kernel

theorem ok939 : check start939 proof939 = true := by
  decide +kernel

theorem ok940 : andB (check start940 proof940) (cpOk (replay start940 proof940) start941) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
