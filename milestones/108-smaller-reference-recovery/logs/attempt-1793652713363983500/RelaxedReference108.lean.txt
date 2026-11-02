import RecoveredReference108

namespace Snake9.RecoveredReference108
open Snake9.LocalWindow
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem relaxed_reference_refuted :
    Refuted (winOf [0, 1, 2, 3, 0, 4])
      [(0, 2), (0, 21), (0, 21), (0, 2), (0, 3)] := by
  let cs : List Tags.Ctr := D012304A22623.ctrs.mapIdx fun i ct =>
    if i ∈ [2, 3, 4, 5, 7, 9] then { ct with k := 21 } else ct
  have hc : Tags.checkAll D012304A22623.meaning cs D012304A22623.window
      [(0, 2), (0, 21), (0, 21), (0, 2), (0, 3)]
      D012304A22623.tags D012304A22623.raw = true := by
    decide +kernel
  apply Tags.refuted_of_sat (f := D012304A22623.cnf) ?_ D012304A22623.unsat
  intro S E h
  exact ⟨Tags.tau S E D012304A22623.meaning cs,
    Tags.sound D012304A22623.meaning cs D012304A22623.window
      [(0, 2), (0, 21), (0, 21), (0, 2), (0, 3)]
      D012304A22623.tags D012304A22623.raw hc S E h⟩

#print axioms relaxed_reference_refuted
end Snake9.RecoveredReference108
