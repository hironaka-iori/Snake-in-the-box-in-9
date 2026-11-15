import LocalWindowCtxUnsat.C70123412A365354K11
import LocalWindowCtxUnsat.C801234523A652633K78
import LocalWindowCtxUnsat.C70123425A656534K23
import LocalWindowCtxUnsat.C70123412A632634K91
import DirectionWindowBridge6SC

/-! Glue test (milestones/35-231-lean/README.md): four of the test certificates give exactly the
 `RefutedCtx7` / `RefutedCtx8` statements of the plan's keys `(dirs, t, level - 1)`. -/

namespace Snake9.DirectionWindow6SC
open Snake9.LocalWindow

theorem ctx7_C70123412A365354K11 : RefutedCtx7 ([0, 1, 2, 3, 4, 1, 2], [3, 6, 5, 3, 5, 4], 11) :=
  TagsSW.refutedShareFrom_of_sat C70123412A365354K11.sat C70123412A365354K11.unsat

theorem ctx8_C801234523A652633K78 : RefutedCtx8 ([0, 1, 2, 3, 4, 5, 2, 3], [6, 5, 2, 6, 3, 3], 78) :=
  TagsSW.refutedShareFrom_of_sat C801234523A652633K78.sat C801234523A652633K78.unsat

theorem ctx7_C70123425A656534K23 : RefutedCtx7 ([0, 1, 2, 3, 4, 2, 5], [6, 5, 6, 5, 3, 4], 23) :=
  TagsSW.refutedShareFrom_of_sat C70123425A656534K23.sat C70123425A656534K23.unsat

theorem ctx7_C70123412A632634K91 : RefutedCtx7 ([0, 1, 2, 3, 4, 1, 2], [6, 3, 2, 6, 3, 4], 91) :=
  TagsSW.refutedShareFrom_of_sat C70123412A632634K91.sat C70123412A632634K91.unsat

end Snake9.DirectionWindow6SC

#print axioms Snake9.DirectionWindow6SC.ctx7_C70123412A365354K11
#print axioms Snake9.DirectionWindow6SC.ctx8_C801234523A652633K78
#print axioms Snake9.DirectionWindow6SC.ctx7_C70123425A656534K23
#print axioms Snake9.DirectionWindow6SC.ctx7_C70123412A632634K91
