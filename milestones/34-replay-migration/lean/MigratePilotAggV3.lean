import LocalWindowTags
import LocalWindowSat.Q012304A26432
import LocalWindowUnsat.Q012304A26432
import LocalWindowSat.Q01234A4244
import LocalWindowUnsat.Q01234A4244
import LocalWindowSat.R012301A34324
import LocalWindowUnsat.R012301A34324

/-! Pilot of milestones/34-replay-migration (checker v3): the forms in which the production
aggregates use a window replay (`LocalWindowDirUnsatR4b`, `LocalWindowDirUnsatR4`,
`LocalWindowDirSatR4`, `LocalWindowDirUnsatReuse7L417d`), for three windows.  The same file is
compiled against the old split replays and against the v3 ones. -/

set_option maxRecDepth 100000

namespace Snake9.LocalWindow

/-- As `LocalWindowDirSatR4b.AllUnsat237`. -/
def PilotUnsat : Prop :=
  Unsat Q012304A26432.cnf ∧
  Unsat Q01234A4244.cnf ∧
  Unsat R012301A34324.cnf

/-- As `LocalWindowDirUnsatR4b.allUnsat237`. -/
theorem pilotUnsat : PilotUnsat :=
  ⟨Q012304A26432.unsat,
   Q01234A4244.unsat,
   R012301A34324.unsat⟩

/-- As `LocalWindowDirUnsatR4.allUnsat236` and `LocalWindowDirUnsatK6.allUnsatK6`. -/
theorem pilotUnsat' : PilotUnsat := by
  unfold PilotUnsat
  refine ⟨Q012304A26432.unsat, ?_⟩
  refine ⟨Q01234A4244.unsat, ?_⟩
  exact R012301A34324.unsat

/-- As `LocalWindowDirSatR4.allRefuted236_of_unsat`. -/
theorem pilotRefuted_of_unsat (h : PilotUnsat) :
    AllRefutedList [([0, 1, 2, 3, 0, 4], [2, 6, 4, 3, 2]), ([0, 1, 2, 3, 4], [4, 2, 4, 4]),
      ([0, 1, 2, 3, 0, 1], [3, 4, 3, 2, 4])] := by
  obtain ⟨h0, h1, h2⟩ := h
  exact
    (And.intro (Tags.refuted_of_sat Q012304A26432.sat h0)
    (And.intro (Tags.refuted_of_sat Q01234A4244.sat h1)
    (And.intro (Tags.refuted_of_sat R012301A34324.sat h2) trivial)))

/-- As `LocalWindowDirUnsatReuse7L417d` (the 234 chain): one `refine` per key. -/
theorem pilotRefuted : AllRefutedList [([0, 1, 2, 3, 0, 4], [2, 6, 4, 3, 2]), ([0, 1, 2, 3, 4], [4, 2, 4, 4]),
      ([0, 1, 2, 3, 0, 1], [3, 4, 3, 2, 4])] := by
  refine ⟨Tags.refuted_of_sat Q012304A26432.sat Q012304A26432.unsat, ?_⟩
  refine ⟨Tags.refuted_of_sat Q01234A4244.sat Q01234A4244.unsat, ?_⟩
  refine ⟨Tags.refuted_of_sat R012301A34324.sat R012301A34324.unsat, ?_⟩
  exact trivial

theorem pilotRefuted' : AllRefutedList [([0, 1, 2, 3, 0, 4], [2, 6, 4, 3, 2]), ([0, 1, 2, 3, 4], [4, 2, 4, 4]),
      ([0, 1, 2, 3, 0, 1], [3, 4, 3, 2, 4])] :=
  pilotRefuted_of_unsat pilotUnsat

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.pilotUnsat
#print axioms Snake9.LocalWindow.pilotUnsat'
#print axioms Snake9.LocalWindow.pilotRefuted
#print axioms Snake9.LocalWindow.pilotRefuted'
