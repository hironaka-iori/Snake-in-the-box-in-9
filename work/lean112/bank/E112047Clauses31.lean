import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1446)) (countLit q [-5]) (countLit q [-7]) (count1445 q) 1 1 (meaningNeg5 q) (meaningNeg7 q) (meaning1446 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 7 = true ∨ valuation q 1446 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1445)) (literal (valuationOf q) (1447)) (countLit q [-3]) (countLit q [-5, -7]) (count1447 q) 1 (meaning1445 q) (meaning1447 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1447 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = true := by
  have hs : count1447 q = (countLit q [-3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (countLit q [-3]) (countLit q [-5, -7]) (count1447 q) 2 (meaning1446 q) (meaning1448 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -7])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1447)) (countLit q [-3]) (countLit q [-5, -7]) (count1447 q) 1 (meaningNeg3 q) (meaning1447 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1447 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1445 = false ∨ valuationOf q 1448 = true := by
  have hs : count1447 q = (countLit q [-3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1448)) (countLit q [-3]) (countLit q [-5, -7]) (count1447 q) 1 1 (meaningNeg3 q) (meaning1445 q) (meaning1448 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1445 = false ∨ valuation q 1448 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true := by
  have hs : count1447 q = (countLit q [-3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (countLit q [-3]) (countLit q [-5, -7]) (count1447 q) 1 2 (meaningNeg3 q) (meaning1446 q) (meaning1449 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1446 = false ∨ valuation q 1449 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1450)) (countLit q [-11]) (countLit q [-12]) (count1450 q) 1 (meaningNeg12 q) (meaning1450 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1450 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1450)) (countLit q [-11]) (countLit q [-12]) (count1450 q) 1 (meaningNeg11 q) (meaning1450 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1450 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1451)) (countLit q [-11]) (countLit q [-12]) (count1450 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning1451 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 1451 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1452)) (countLit q [-14]) (countLit q [-17]) (count1452 q) 1 (meaningNeg17 q) (meaning1452 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1452 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1452)) (countLit q [-14]) (countLit q [-17]) (count1452 q) 1 (meaningNeg14 q) (meaning1452 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1452 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1453)) (countLit q [-14]) (countLit q [-17]) (count1452 q) 1 1 (meaningNeg14 q) (meaningNeg17 q) (meaning1453 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 1453 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1454)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 1 (meaning1452 q) (meaning1454 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1454 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1455)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 2 (meaning1453 q) (meaning1455 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1455 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 1 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1455)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 1 1 (meaning1450 q) (meaning1452 q) (meaning1455 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1452 = false ∨ valuation q 1455 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1456)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 1 2 (meaning1450 q) (meaning1453 q) (meaning1456 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1453 = false ∨ valuation q 1456 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 2 (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1455 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 2 1 (meaning1451 q) (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1452 = false ∨ valuation q 1456 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-11, -12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-11, -12]) (countLit q [-14, -17]) (count1454 q) 2 2 (meaning1451 q) (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1453 = false ∨ valuation q 1457 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1458 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1458)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 1 (meaning1454 q) (meaning1458 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1458 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1459)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 2 (meaning1455 q) (meaning1459 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1459 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1460 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1460)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 3 (meaning1456 q) (meaning1460 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1460 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1461 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1461)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 4 (meaning1457 q) (meaning1461 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1461 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1458 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_left (literal (valuationOf q) (1447)) (literal (valuationOf q) (1458)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 1 (meaning1447 q) (meaning1458 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1458 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1459)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 1 1 (meaning1447 q) (meaning1454 q) (meaning1459 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1454 = false ∨ valuation q 1459 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1460)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 1 2 (meaning1447 q) (meaning1455 q) (meaning1460 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1455 = false ∨ valuation q 1460 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_left (literal (valuationOf q) (1448)) (literal (valuationOf q) (1459)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 2 (meaning1448 q) (meaning1459 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1459 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1460 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1460)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 2 1 (meaning1448 q) (meaning1454 q) (meaning1460 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1454 = false ∨ valuation q 1460 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1461 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1461)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 2 2 (meaning1448 q) (meaning1455 q) (meaning1461 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1455 = false ∨ valuation q 1461 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1462 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1462)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 2 3 (meaning1448 q) (meaning1456 q) (meaning1462 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1456 = false ∨ valuation q 1462 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1463 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1463)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 2 4 (meaning1448 q) (meaning1457 q) (meaning1463 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1457 = false ∨ valuation q 1463 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E047.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112047
