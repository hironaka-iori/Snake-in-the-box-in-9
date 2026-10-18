import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1461)) (countLit q [-27]) (countLit q [-29, -30]) (count1459 q) 1 2 (meaningNeg27 q) (meaning1458 q) (meaning1461 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1458 = false ∨ valuation q 1461 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1462)) (countLit q [-33]) (countLit q [-35]) (count1462 q) 1 (meaningNeg35 q) (meaning1462 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1462 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1462)) (countLit q [-33]) (countLit q [-35]) (count1462 q) 1 (meaningNeg33 q) (meaning1462 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1462 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1463)) (countLit q [-33]) (countLit q [-35]) (count1462 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning1463 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 1463 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-37]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1464)) (countLit q [-37]) (countLit q [-41]) (count1464 q) 1 (meaningNeg41 q) (meaning1464 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1464 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-37]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1464)) (countLit q [-37]) (countLit q [-41]) (count1464 q) 1 (meaningNeg37 q) (meaning1464 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1464 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-37]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1465)) (countLit q [-37]) (countLit q [-41]) (count1464 q) 1 1 (meaningNeg37 q) (meaningNeg41 q) (meaning1465 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 41 = true ∨ valuation q 1465 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 1 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 2 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 1 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 1 1 (meaning1462 q) (meaning1464 q) (meaning1467 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 1 2 (meaning1462 q) (meaning1465 q) (meaning1468 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 2 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 2 1 (meaning1463 q) (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1464 = false ∨ valuation q 1468 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1469 = true := by
  have hs : count1466 q = (countLit q [-33, -35]) + (countLit q [-37, -41]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -41])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1469)) (countLit q [-33, -35]) (countLit q [-37, -41]) (count1466 q) 2 2 (meaning1463 q) (meaning1465 q) (meaning1469 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = false ∨ valuation q 1469 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 1 1 (meaning1459 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 1 2 (meaning1459 q) (meaning1467 q) (meaning1472 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1467 = false ∨ valuation q 1472 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1473)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 1 3 (meaning1459 q) (meaning1468 q) (meaning1473 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1468 = false ∨ valuation q 1473 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1474 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1474)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 1 4 (meaning1459 q) (meaning1469 q) (meaning1474 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1469 = false ∨ valuation q 1474 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1471)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 2 (meaning1460 q) (meaning1471 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1471 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 2 1 (meaning1460 q) (meaning1466 q) (meaning1472 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1466 = false ∨ valuation q 1472 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 2 2 (meaning1460 q) (meaning1467 q) (meaning1473 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1467 = false ∨ valuation q 1473 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1474 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1474)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 2 3 (meaning1460 q) (meaning1468 q) (meaning1474 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1468 = false ∨ valuation q 1474 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1475 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1475)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 2 4 (meaning1460 q) (meaning1469 q) (meaning1475 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1469 = false ∨ valuation q 1475 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1472)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 3 (meaning1461 q) (meaning1472 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1472 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 3 1 (meaning1461 q) (meaning1466 q) (meaning1473 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1466 = false ∨ valuation q 1473 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1474 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 3 2 (meaning1461 q) (meaning1467 q) (meaning1474 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1467 = false ∨ valuation q 1474 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1475 = true := by
  have hs : count1470 q = (countLit q [-27, -29, -30]) + (countLit q [-33, -35, -37, -41]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-33, -35, -37, -41])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1475)) (countLit q [-27, -29, -30]) (countLit q [-33, -35, -37, -41]) (count1470 q) 3 3 (meaning1461 q) (meaning1468 q) (meaning1475 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1468 = false ∨ valuation q 1475 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1477)) (countLit q [-43]) (countLit q [-44]) (count1477 q) 1 (meaningNeg44 q) (meaning1477 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1477 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1477)) (countLit q [-43]) (countLit q [-44]) (count1477 q) 1 (meaningNeg43 q) (meaning1477 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1477 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1478)) (countLit q [-43]) (countLit q [-44]) (count1477 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning1478 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 1478 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1479)) (countLit q [-46]) (countLit q [-49]) (count1479 q) 1 (meaningNeg49 q) (meaning1479 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1479 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E064.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112064
