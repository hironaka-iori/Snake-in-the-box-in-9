import LocalWindowUnsat.ShareWindow144.Data242
import LocalWindowUnsat.ShareWindow144.Data243

/-! Kernel checks of segments 965-968 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok965 : check start965 proof965 = true := by
  decide +kernel

theorem ok966 : check start966 proof966 = true := by
  decide +kernel

theorem ok967 : check start967 proof967 = true := by
  decide +kernel

theorem ok968 : andB (check start968 proof968) (cpOk (replay start968 proof968) start969) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
