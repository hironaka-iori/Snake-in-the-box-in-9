import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1428)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 3 3 (meaning1359 q) (meaning1412 q) (meaning1428 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1412 = false ∨ valuation q 1428 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1429)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 3 4 (meaning1359 q) (meaning1413 q) (meaning1429 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1413 = false ∨ valuation q 1429 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1430)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 3 5 (meaning1359 q) (meaning1414 q) (meaning1430 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1414 = false ∨ valuation q 1430 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1431 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1431)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 3 6 (meaning1359 q) (meaning1415 q) (meaning1431 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1415 = false ∨ valuation q 1431 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1432 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1432)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 3 7 (meaning1359 q) (meaning1416 q) (meaning1432 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1416 = false ∨ valuation q 1432 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1430)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 4 4 (meaning1360 q) (meaning1413 q) (meaning1430 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1413 = false ∨ valuation q 1430 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1431 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1431)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 4 5 (meaning1360 q) (meaning1414 q) (meaning1431 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1414 = false ∨ valuation q 1431 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) + (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (l₂ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1310)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1448)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1436 q) 3 10 (meaning1310 q) (meaning1432 q) (meaning1448 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1432 = false ∨ valuation q 1448 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) + (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (l₂ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1448)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1436 q) 4 9 (meaning1311 q) (meaning1431 q) (meaning1448 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1431 = false ∨ valuation q 1448 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) + (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (l₂ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1448)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1436 q) 5 8 (meaning1312 q) (meaning1430 q) (meaning1448 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1430 = false ∨ valuation q 1448 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) + (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (l₂ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1448)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1436 q) 6 7 (meaning1313 q) (meaning1429 q) (meaning1448 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1429 = false ∨ valuation q 1448 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) + (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (l₂ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1314)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1448)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1436 q) 7 6 (meaning1314 q) (meaning1428 q) (meaning1448 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1428 = false ∨ valuation q 1448 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) + (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (l₂ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1315)) (literal (valuationOf q) (1427)) (literal (valuationOf q) (1448)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1436 q) 8 5 (meaning1315 q) (meaning1427 q) (meaning1448 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1427 = false ∨ valuation q 1448 = true := counterClause621 (baseVal q)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false := by
  rw [value1448]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1436 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value23, value25, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value49, value50, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (244 : Vertex) (245 : Vertex) (252 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value73, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (387 : Vertex) (393 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value75, value76, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (397 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value80, value81, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (400 : Vertex) (402 : Vertex) (404 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value80, value81, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (400 : Vertex) (402 : Vertex) (408 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value83, value84, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (404 : Vertex) (406 : Vertex) (412 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value85, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (408 : Vertex) (410 : Vertex) (412 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E094.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h⟩

end
end Snake9.Regrowth.E112094
