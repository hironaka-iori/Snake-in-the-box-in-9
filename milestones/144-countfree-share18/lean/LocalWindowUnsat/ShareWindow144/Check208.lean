import LocalWindowUnsat.ShareWindow144.Data208
import LocalWindowUnsat.ShareWindow144.Data209

/-! Kernel checks of segments 829-832 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok829 : check start829 proof829 = true := by
  decide +kernel

theorem ok830 : check start830 proof830 = true := by
  decide +kernel

theorem ok831 : check start831 proof831 = true := by
  decide +kernel

theorem ok832 : andB (check start832 proof832) (cpOk (replay start832 proof832) start833) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
