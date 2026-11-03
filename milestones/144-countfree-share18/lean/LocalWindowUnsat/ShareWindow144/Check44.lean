import LocalWindowUnsat.ShareWindow144.Data44
import LocalWindowUnsat.ShareWindow144.Data45

/-! Kernel checks of segments 173-176 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok173 : check start173 proof173 = true := by
  decide +kernel

theorem ok174 : check start174 proof174 = true := by
  decide +kernel

theorem ok175 : check start175 proof175 = true := by
  decide +kernel

theorem ok176 : andB (check start176 proof176) (cpOk (replay start176 proof176) start177) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
