import LocalWindowUnsat.C223RevRepeated.Data10

/-! Kernel checks of segments 9-10 of `223_rev_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C223RevRepeated
open Snake9.Lrat

theorem ok9 : andB (check start9 proof9) (cpOk (replay start9 proof9) cp10) = true := by
  decide +kernel

theorem ok10 : andB (check start10 proof10) (hasEmpty (replay start10 proof10) 994) = true := by
  decide +kernel

end Snake9.LocalWindow.C223RevRepeated
