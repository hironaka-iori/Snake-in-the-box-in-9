import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1457 = true := by
  have hs : count1452 q = (countLit q [-81, -82, -83, -86, -88, -90, -93]) + (countLit q [-95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -86, -88, -90, -93]) (l₂ := [-95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1457)) (countLit q [-81, -82, -83, -86, -88, -90, -93]) (countLit q [-95, -96, -97, -100, -102, -103, -105]) (count1452 q) 5 1 (meaning1429 q) (meaning1445 q) (meaning1457 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1445 = false ∨ valuation q 1457 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1471)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 2 5 (meaning1400 q) (meaning1456 q) (meaning1471 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1456 = false ∨ valuation q 1471 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1472)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 2 6 (meaning1400 q) (meaning1457 q) (meaning1472 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1457 = false ∨ valuation q 1472 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1470)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 3 3 (meaning1401 q) (meaning1454 q) (meaning1470 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1454 = false ∨ valuation q 1470 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1471)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 3 4 (meaning1401 q) (meaning1455 q) (meaning1471 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1455 = false ∨ valuation q 1471 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1472)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 3 5 (meaning1401 q) (meaning1456 q) (meaning1472 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1456 = false ∨ valuation q 1472 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1471)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 4 3 (meaning1402 q) (meaning1454 q) (meaning1471 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1454 = false ∨ valuation q 1471 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1472)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 4 4 (meaning1402 q) (meaning1455 q) (meaning1472 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1455 = false ∨ valuation q 1472 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1472)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 5 3 (meaning1403 q) (meaning1454 q) (meaning1472 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1454 = false ∨ valuation q 1472 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) + (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (l₂ := [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1473)) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79]) (countLit q [-81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1465 q) 5 4 (meaning1403 q) (meaning1455 q) (meaning1473 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1455 = false ∨ valuation q 1473 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) + (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (l₂ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1478 q) 4 9 (meaning1353 q) (meaning1473 q) (meaning1490 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1473 = false ∨ valuation q 1490 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) + (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (l₂ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1478 q) 5 8 (meaning1354 q) (meaning1472 q) (meaning1490 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1472 = false ∨ valuation q 1490 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) + (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (l₂ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1478 q) 6 7 (meaning1355 q) (meaning1471 q) (meaning1490 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1471 = false ∨ valuation q 1490 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) + (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (l₂ := [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26, -28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (countLit q [-54, -55, -57, -60, -61, -64, -65, -67, -70, -71, -73, -76, -79, -81, -82, -83, -86, -88, -90, -93, -95, -96, -97, -100, -102, -103, -105]) (count1478 q) 7 6 (meaning1356 q) (meaning1470 q) (meaning1490 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1470 = false ∨ valuation q 1490 = true := counterClause366 (baseVal q)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false := by
  rw [value1490]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1478 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value3, value4, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (37 : Vertex) (52 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value61, value62, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (290 : Vertex) (291 : Vertex) (306 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value94, value95, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (452 : Vertex) (453 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E246.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h⟩

end
end Snake9.Regrowth.E112246
