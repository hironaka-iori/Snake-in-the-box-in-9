/-
The premises of `upper_of_refuted6SC_noShare` for the toy tables `tables6SCToy` (milestone 35):
the two context share certificates (LRAT-replayed), the ctx covers, the empty k6/H8 covers and the
step test; plus a unit test of the witness-driven shard check on one label whose ctx 7 field is
decisive.  Core Lean.
-/
import DirectionWindowBridge6SC
import WindowAutomaton6SCV2
import WindowAutomaton6SCToyData
import LocalWindowCtxUnsat.C70123412A236664K15
import LocalWindowCtxUnsat.C801234032A544643K15

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.DirectionWindow6SC
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow6 Snake9.DirectionWindow6S

/-! ## The certificates -/

theorem ctx7_C70123412A236664K15 : RefutedCtx7 ([0, 1, 2, 3, 4, 1, 2], [2, 3, 6, 6, 6, 4], 15) :=
  TagsSW.refutedShareFrom_of_sat C70123412A236664K15.sat C70123412A236664K15.unsat

theorem ctx8_C801234032A544643K15 : RefutedCtx8 ([0, 1, 2, 3, 4, 0, 3, 2], [5, 4, 4, 6, 4, 3], 15) :=
  TagsSW.refutedShareFrom_of_sat C801234032A544643K15.sat C801234032A544643K15.unsat

theorem allCtx7_6SCToy : AllP RefutedCtx7 ctx7Keys6SCToy := ⟨ctx7_C70123412A236664K15, trivial⟩
theorem allCtx8_6SCToy : AllP RefutedCtx8 ctx8Keys6SCToy := ⟨ctx8_C801234032A544643K15, trivial⟩

/-! ## The ctx covers -/

theorem ctxZero7_6SCToy :
    allRGS 7 0 (zeroOutsideC (rowf7 tables6SCToy) ctx7Shapes6SCToy) = true := by decide +kernel

theorem ctxRow7_6SCToy_0 :
    allSym (ctxRowOK tables6SCToy.cbits (rowf7 tables6SCToy [0, 1, 2, 3, 4, 1, 2])
      (ctx7Chunks6SCToy.getD 0 []) [0, 1, 2, 3, 4, 1, 2]) = true := by decide +kernel

theorem ctxCover7_6SCToy : CtxCover 7 tables6SCToy.cbits (rowf7 tables6SCToy) ctx7Keys6SCToy :=
  ctxCover_rows ctx7Shapes6SCToy ctxZero7_6SCToy (fun c hc => by
    simp only [ctx7Shapes6SCToy, List.mem_singleton] at hc
    subst hc
    exact ⟨0, ctxRow7_6SCToy_0⟩)

theorem ctxZero8_6SCToy :
    allRGS 8 0 (zeroOutsideC (rowf8 tables6SCToy) ctx8Shapes6SCToy) = true := by decide +kernel

theorem ctxRow8_6SCToy_0 :
    allSym (ctxRowOK tables6SCToy.cbits (rowf8 tables6SCToy [0, 1, 2, 3, 4, 0, 3, 2])
      (ctx8Chunks6SCToy.getD 0 []) [0, 1, 2, 3, 4, 0, 3, 2]) = true := by decide +kernel

theorem ctxCover8_6SCToy : CtxCover 8 tables6SCToy.cbits (rowf8 tables6SCToy) ctx8Keys6SCToy :=
  ctxCover_rows ctx8Shapes6SCToy ctxZero8_6SCToy (fun c hc => by
    simp only [ctx8Shapes6SCToy, List.mem_singleton] at hc
    subst hc
    exact ⟨0, ctxRow8_6SCToy_0⟩)

/-- The two ctx fields are where the keys say, with the level `K + 1 = 16`. -/
example : ctx7A tables6SCToy [5, 0, 3, 6, 8, 0, 3] [2, 3, 6, 6, 6, 4] = 16 := by decide +kernel
example : ctx8A tables6SCToy [1, 7, 2, 3, 4, 1, 3, 2] [5, 4, 4, 6, 4, 3] = 16 := by decide +kernel
example : ctx7A tables6SCToy [5, 0, 3, 6, 8, 0, 3] [2, 3, 6, 6, 6, 5] = 0 := by decide +kernel

/-! ## The empty k6 and H8 parts -/

theorem k6Zero_3 : allRGS 3 0 (zeroOutside6 tables6SCToy.s.k6 []) = true := by decide +kernel
theorem k6Zero_4 : allRGS 4 0 (zeroOutside6 tables6SCToy.s.k6 []) = true := by decide +kernel
theorem k6Zero_5 : allRGS 5 0 (zeroOutside6 tables6SCToy.s.k6 []) = true := by decide +kernel
theorem k6Zero_6 : allRGS 6 0 (zeroOutside6 tables6SCToy.s.k6 []) = true := by decide +kernel
theorem k6Zero_7 : allRGS 7 0 (zeroOutside6 tables6SCToy.s.k6 []) = true := by decide +kernel

theorem cover6_6SCToy : Cover6 tables6SCToy.s.k6 [] :=
  cover6_chunks (T := tables6SCToy.s.k6) [] [] k6Zero_3 k6Zero_4 k6Zero_5 k6Zero_6 k6Zero_7
    (fun r hr => absurd hr List.not_mem_nil)

theorem coverH8_6SCToy : CoverH8 tables6SCToy.s [] := rfl

/-! ## The step test -/

theorem stepOK6SCToy : StepOK6SC tables6SCToy :=
  stepOK6SC_of_trivial _ (fun _ _ => rfl) (by decide)

/-! ## Unit test of the witness-driven check (`check6SCAtW`, code 13)

The variant `tables6SCToy496` has `num = 496 = 120 * 4 + 16`.  On the label `c = 01234523`,
`t0 = 2` (so `canon (c.drop 1) = 0123412`), the transition `(3, 6, 6, 6, 4)` passes with code 13
(the ctx 7 field 16) and fails with code 0 (the 5-window share field 0); `check6SCAt_of_W` turns a
passing witness into `check6SCAt`.  -/

def tables6SCToy496 : Tables6SC := { tables6SCToy with s := { tables6SCToyS with k6 := { tables6SCToyk6 with num := 496 } } }

example : tr6SCF tables6SCToy496 [0, 1, 2, 3, 4, 5, 2, 3] 0 0 0
    (c7Rows6SCToy 1 2) 0 2 3 6 6 6 4 13 = true := by decide +kernel
example : tr6SCF tables6SCToy496 [0, 1, 2, 3, 4, 5, 2, 3] 0 0 0
    (c7Rows6SCToy 1 2) 0 2 3 6 6 6 4 0 = false := by decide +kernel

/-- A full label of `tables6SCToy` (all 7,776 transitions) through `check6SCAtW` with code 13 on
every transition (the witness literal is 7,776 hex digits `d`), and its consequence `check6SCAt` by the bridge. -/
theorem label6SCToy_w : check6SCAtW tables6SCToy [0, 1, 2, 3, 4, 5, 2, 3] 2
    (nat_lit 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd) = true := by
  decide +kernel

theorem label6SCToy : check6SCAt tables6SCToy [0, 1, 2, 3, 4, 5, 2, 3] 2 = true :=
  check6SCAt_of_W _ _ _ _ label6SCToy_w

end Snake9.DirectionWindow6SC

#print axioms Snake9.DirectionWindow6SC.ctx7_C70123412A236664K15
#print axioms Snake9.DirectionWindow6SC.ctx8_C801234032A544643K15
#print axioms Snake9.DirectionWindow6SC.ctxCover7_6SCToy
#print axioms Snake9.DirectionWindow6SC.ctxCover8_6SCToy
#print axioms Snake9.DirectionWindow6SC.label6SCToy
