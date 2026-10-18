import E112182Semantics
import B112E182Inputs
namespace Snake9.Regrowth.E112182
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1392 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1392)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 1 3 (meaning1341 q) (meaning1383 q) (meaning1392 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1383 = false ∨ valuation q 1392 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1393 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1393)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 1 4 (meaning1341 q) (meaning1384 q) (meaning1393 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1384 = false ∨ valuation q 1393 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1392 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1392)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 2 2 (meaning1342 q) (meaning1382 q) (meaning1392 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1382 = false ∨ valuation q 1392 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1393 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1393)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 2 3 (meaning1342 q) (meaning1383 q) (meaning1393 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1383 = false ∨ valuation q 1393 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1394 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1394)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 2 4 (meaning1342 q) (meaning1384 q) (meaning1394 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1384 = false ∨ valuation q 1394 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1393 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1393)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 3 2 (meaning1343 q) (meaning1382 q) (meaning1393 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1382 = false ∨ valuation q 1393 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1393 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1393)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 4 1 (meaning1344 q) (meaning1381 q) (meaning1393 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1381 = false ∨ valuation q 1393 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1394 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1394)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 4 2 (meaning1344 q) (meaning1382 q) (meaning1394 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1382 = false ∨ valuation q 1394 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true := by
  have hs : count1397 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) + (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (l₂ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1404)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1397 q) 2 6 (meaning1302 q) (meaning1394 q) (meaning1404 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1394 = false ∨ valuation q 1404 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1404 = true := by
  have hs : count1397 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) + (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (l₂ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1303)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1404)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1397 q) 3 5 (meaning1303 q) (meaning1393 q) (meaning1404 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1393 = false ∨ valuation q 1404 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1404 = true := by
  have hs : count1397 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) + (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (l₂ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1404)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1397 q) 4 4 (meaning1304 q) (meaning1392 q) (meaning1404 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1392 = false ∨ valuation q 1404 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 1305 = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1404 = true := by
  have hs : count1397 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) + (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (l₂ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1305)) (literal (valuationOf q) (1391)) (literal (valuationOf q) (1404)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1397 q) 5 3 (meaning1305 q) (meaning1391 q) (meaning1404 q) hs
  change valuationOf q 1305 = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 1305 = false ∨ valuation q 1391 = false ∨ valuation q 1404 = true := counterClause236 (baseVal q)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false := by
  rw [value1404]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1397 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem block7 (q : Snake 81) (h : Conditions q) : B112E182.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h⟩

end
end Snake9.Regrowth.E112182
