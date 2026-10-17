import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1479)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 2 2 (meaning1466 q) (meaning1473 q) (meaning1479 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1473 = false ∨ valuation q 1479 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 2 3 (meaning1466 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 2 4 (meaning1466 q) (meaning1475 q) (meaning1481 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1475 = false ∨ valuation q 1481 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1478)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 3 (meaning1467 q) (meaning1478 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1478 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1479)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 3 1 (meaning1467 q) (meaning1472 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1472 = false ∨ valuation q 1479 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1480)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 3 2 (meaning1467 q) (meaning1473 q) (meaning1480 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1473 = false ∨ valuation q 1480 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1483)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 1 (meaning1476 q) (meaning1483 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1483 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_left (literal (valuationOf q) (1456)) (literal (valuationOf q) (1483)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 1 (meaning1456 q) (meaning1483 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1483 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1484 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1484)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 1 1 (meaning1456 q) (meaning1476 q) (meaning1484 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1476 = false ∨ valuation q 1484 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1485 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1485)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 1 2 (meaning1456 q) (meaning1477 q) (meaning1485 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1477 = false ∨ valuation q 1485 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 1 3 (meaning1456 q) (meaning1478 q) (meaning1486 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1478 = false ∨ valuation q 1486 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1487)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 1 4 (meaning1456 q) (meaning1479 q) (meaning1487 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1479 = false ∨ valuation q 1487 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1485 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1485)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 2 1 (meaning1457 q) (meaning1476 q) (meaning1485 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1476 = false ∨ valuation q 1485 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1486 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1486)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 2 2 (meaning1457 q) (meaning1477 q) (meaning1486 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1477 = false ∨ valuation q 1486 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1487)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 2 3 (meaning1457 q) (meaning1478 q) (meaning1487 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1478 = false ∨ valuation q 1487 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 2 4 (meaning1457 q) (meaning1479 q) (meaning1488 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1479 = false ∨ valuation q 1488 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 2 5 (meaning1457 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1486 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1486)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 3 1 (meaning1458 q) (meaning1476 q) (meaning1486 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1476 = false ∨ valuation q 1486 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1487 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1487)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 3 2 (meaning1458 q) (meaning1477 q) (meaning1487 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1477 = false ∨ valuation q 1487 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1488)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 3 3 (meaning1458 q) (meaning1478 q) (meaning1488 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1478 = false ∨ valuation q 1488 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1489)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 3 4 (meaning1458 q) (meaning1479 q) (meaning1489 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1479 = false ∨ valuation q 1489 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1487 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1487)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 4 1 (meaning1459 q) (meaning1476 q) (meaning1487 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1476 = false ∨ valuation q 1487 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 4 2 (meaning1459 q) (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1477 = false ∨ valuation q 1488 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 4 3 (meaning1459 q) (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1478 = false ∨ valuation q 1489 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 4 4 (meaning1459 q) (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1479 = false ∨ valuation q 1490 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 4 5 (meaning1459 q) (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1480 = false ∨ valuation q 1491 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1492)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 4 6 (meaning1459 q) (meaning1481 q) (meaning1492 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1481 = false ∨ valuation q 1492 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1488)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 5 1 (meaning1460 q) (meaning1476 q) (meaning1488 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1476 = false ∨ valuation q 1488 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1489)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 5 2 (meaning1460 q) (meaning1477 q) (meaning1489 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1477 = false ∨ valuation q 1489 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1490)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 5 3 (meaning1460 q) (meaning1478 q) (meaning1490 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1478 = false ∨ valuation q 1490 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1491)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 5 4 (meaning1460 q) (meaning1479 q) (meaning1491 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1479 = false ∨ valuation q 1491 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1492)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 5 5 (meaning1460 q) (meaning1480 q) (meaning1492 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1480 = false ∨ valuation q 1492 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E161.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112161
