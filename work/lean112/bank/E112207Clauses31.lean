import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1456)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 4 (meaning1425 q) (meaning1447 q) (meaning1456 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1447 = false ∨ valuation q 1456 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1457 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1457)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 5 (meaning1425 q) (meaning1448 q) (meaning1457 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1448 = false ∨ valuation q 1457 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1458 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1458)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 6 (meaning1425 q) (meaning1449 q) (meaning1458 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1449 = false ∨ valuation q 1458 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1453)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 (meaning1426 q) (meaning1453 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1453 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1454 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1454)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 1 (meaning1426 q) (meaning1444 q) (meaning1454 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1444 = false ∨ valuation q 1454 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1455)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 2 (meaning1426 q) (meaning1445 q) (meaning1455 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1445 = false ∨ valuation q 1455 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1456)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 3 (meaning1426 q) (meaning1446 q) (meaning1456 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1446 = false ∨ valuation q 1456 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1457 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1457)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 4 (meaning1426 q) (meaning1447 q) (meaning1457 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1447 = false ∨ valuation q 1457 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1458 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1458)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 5 (meaning1426 q) (meaning1448 q) (meaning1458 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1448 = false ∨ valuation q 1458 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1459)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 6 (meaning1426 q) (meaning1449 q) (meaning1459 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1449 = false ∨ valuation q 1459 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1456 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1456)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 4 2 (meaning1427 q) (meaning1445 q) (meaning1456 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1445 = false ∨ valuation q 1456 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1457 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1457)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 4 3 (meaning1427 q) (meaning1446 q) (meaning1457 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1446 = false ∨ valuation q 1457 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1458 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1458)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 4 4 (meaning1427 q) (meaning1447 q) (meaning1458 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1447 = false ∨ valuation q 1458 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1459 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1459)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 4 5 (meaning1427 q) (meaning1448 q) (meaning1459 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1448 = false ∨ valuation q 1459 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1460 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1460)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 4 6 (meaning1427 q) (meaning1449 q) (meaning1460 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1449 = false ∨ valuation q 1460 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1457 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1457)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 5 2 (meaning1428 q) (meaning1445 q) (meaning1457 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1445 = false ∨ valuation q 1457 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1458 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1458)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 5 3 (meaning1428 q) (meaning1446 q) (meaning1458 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1446 = false ∨ valuation q 1458 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-31]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1465)) (countLit q [-31]) (countLit q [-35]) (count1465 q) 1 (meaningNeg35 q) (meaning1465 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1465 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-31]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1465)) (countLit q [-31]) (countLit q [-35]) (count1465 q) 1 (meaningNeg31 q) (meaning1465 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1465 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-31]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1466)) (countLit q [-31]) (countLit q [-35]) (count1465 q) 1 1 (meaningNeg31 q) (meaningNeg35 q) (meaning1466 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 1466 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-30]) (countLit q [-31, -35]) (count1467 q) 1 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1468)) (countLit q [-30]) (countLit q [-31, -35]) (count1467 q) 2 (meaning1466 q) (meaning1468 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1468 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1467)) (countLit q [-30]) (countLit q [-31, -35]) (count1467 q) 1 (meaningNeg30 q) (meaning1467 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1467 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-30]) (countLit q [-31, -35]) (count1467 q) 1 1 (meaningNeg30 q) (meaning1465 q) (meaning1468 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true := by
  have hs : count1467 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1469)) (countLit q [-30]) (countLit q [-31, -35]) (count1467 q) 1 2 (meaningNeg30 q) (meaning1466 q) (meaning1469 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1466 = false ∨ valuation q 1469 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1470)) (countLit q [-37]) (countLit q [-38]) (count1470 q) 1 (meaningNeg38 q) (meaning1470 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1470 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1470)) (countLit q [-37]) (countLit q [-38]) (count1470 q) 1 (meaningNeg37 q) (meaning1470 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1470 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1471)) (countLit q [-37]) (countLit q [-38]) (count1470 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning1471 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 1471 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-39]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (1472)) (countLit q [-39]) (countLit q [-43]) (count1472 q) 1 (meaningNeg43 q) (meaning1472 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1472 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-39]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1472)) (countLit q [-39]) (countLit q [-43]) (count1472 q) 1 (meaningNeg39 q) (meaning1472 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1472 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 43 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-39]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (1473)) (countLit q [-39]) (countLit q [-43]) (count1472 q) 1 1 (meaningNeg39 q) (meaningNeg43 q) (meaning1473 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 43 = true ∨ valuation q 1473 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-37, -38]) + (countLit q [-39, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-39, -43])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-37, -38]) (countLit q [-39, -43]) (count1474 q) 1 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E207.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112207
