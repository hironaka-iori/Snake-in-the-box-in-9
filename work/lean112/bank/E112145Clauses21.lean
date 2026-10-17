import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1409 = true := by
  have hs : count1409 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1409)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1409 q) 1 (meaning1405 q) (meaning1409 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1409 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1409 = true := by
  have hs : count1409 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1398)) (literal (valuationOf q) (1409)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1409 q) 1 (meaning1398 q) (meaning1409 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1409 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1410 = true := by
  have hs : count1409 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1410)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1409 q) 1 1 (meaning1398 q) (meaning1405 q) (meaning1410 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1405 = false ∨ valuation q 1410 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-79, -83, -84, -85, -86, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -83, -84, -85, -86, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1417)) (countLit q [-79, -83, -84, -85, -86, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1416 q) 1 1 (meaning1390 q) (meaning1409 q) (meaning1417 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1409 = false ∨ valuation q 1417 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-79, -83, -84, -85, -86, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -83, -84, -85, -86, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-79, -83, -84, -85, -86, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1416 q) 1 2 (meaning1390 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1369)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1429)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 2 (meaning1369 q) (meaning1417 q) (meaning1429 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1417 = false ∨ valuation q 1429 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1370)) (literal (valuationOf q) (1428)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 (meaning1370 q) (meaning1428 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1428 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1430)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 2 (meaning1370 q) (meaning1417 q) (meaning1430 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1417 = false ∨ valuation q 1430 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1431)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 3 (meaning1370 q) (meaning1418 q) (meaning1431 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1418 = false ∨ valuation q 1431 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1371)) (literal (valuationOf q) (1429)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 (meaning1371 q) (meaning1429 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1429 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1431)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 2 (meaning1371 q) (meaning1417 q) (meaning1431 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1417 = false ∨ valuation q 1431 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1432)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 3 (meaning1371 q) (meaning1418 q) (meaning1432 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1418 = false ∨ valuation q 1432 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1372)) (literal (valuationOf q) (1430)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 4 (meaning1372 q) (meaning1430 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1430 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1432)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 4 2 (meaning1372 q) (meaning1417 q) (meaning1432 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1417 = false ∨ valuation q 1432 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1433)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 4 3 (meaning1372 q) (meaning1418 q) (meaning1433 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1418 = false ∨ valuation q 1433 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) + (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (l₂ := [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1433)) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]) (countLit q [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 5 2 (meaning1373 q) (meaning1417 q) (meaning1433 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1417 = false ∨ valuation q 1433 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1448 = true := by
  have hs : count1438 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) + (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (l₂ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1325)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1448)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1438 q) 4 7 (meaning1325 q) (meaning1433 q) (meaning1448 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1433 = false ∨ valuation q 1448 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1448 = true := by
  have hs : count1438 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) + (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (l₂ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1326)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1448)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1438 q) 5 6 (meaning1326 q) (meaning1432 q) (meaning1448 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1432 = false ∨ valuation q 1448 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1448 = true := by
  have hs : count1438 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) + (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (l₂ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1448)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1438 q) 6 5 (meaning1327 q) (meaning1431 q) (meaning1448 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1431 = false ∨ valuation q 1448 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1448 = true := by
  have hs : count1438 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) + (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (l₂ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1448)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1438 q) 7 4 (meaning1328 q) (meaning1430 q) (meaning1448 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1430 = false ∨ valuation q 1448 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1448 = true := by
  have hs : count1438 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) + (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (l₂ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1448)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1438 q) 8 3 (meaning1329 q) (meaning1429 q) (meaning1448 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1429 = false ∨ valuation q 1448 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1448 = true := by
  have hs : count1438 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) + (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (l₂ := [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1448)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (countLit q [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]) (count1438 q) 9 2 (meaning1330 q) (meaning1428 q) (meaning1448 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1428 = false ∨ valuation q 1448 = true := counterClause694 (baseVal q)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false := by
  rw [value1448]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1438 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 35 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value1, value35, value67, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (128 : Vertex) (256 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value10, value11, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (38 : Vertex) (44 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value40, value41, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (137 : Vertex) (200 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E145.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h⟩

end
end Snake9.Regrowth.E112145
