import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 74 = true ∨ valuationOf q 996 = true := by
  have hs : count995 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (996)) (countLit q [-73]) (countLit q [-74]) (count995 q) 1 1 (meaningNeg73 q) (meaningNeg74 q) (meaning996 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 996 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (995)) (literal (valuationOf q) (997)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 1 (meaning995 q) (meaning997 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 997 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (996)) (literal (valuationOf q) (998)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 2 (meaning996 q) (meaning998 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 998 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_left (literal (valuationOf q) (993)) (literal (valuationOf q) (997)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 1 (meaning993 q) (meaning997 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 997 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (995)) (literal (valuationOf q) (998)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 1 1 (meaning993 q) (meaning995 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 995 = false ∨ valuation q 998 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (996)) (literal (valuationOf q) (999)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 1 2 (meaning993 q) (meaning996 q) (meaning999 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 996 = false ∨ valuation q 999 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_left (literal (valuationOf q) (994)) (literal (valuationOf q) (998)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 2 (meaning994 q) (meaning998 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 998 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (995)) (literal (valuationOf q) (999)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 2 1 (meaning994 q) (meaning995 q) (meaning999 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 995 = false ∨ valuation q 999 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true := by
  have hs : count997 q = (countLit q [-69, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (996)) (literal (valuationOf q) (1000)) (countLit q [-69, -72]) (countLit q [-73, -74]) (count997 q) 2 2 (meaning994 q) (meaning996 q) (meaning1000 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 996 = false ∨ valuation q 1000 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_right (literal (valuationOf q) (997)) (literal (valuationOf q) (1001)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 1 (meaning997 q) (meaning1001 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1001 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_right (literal (valuationOf q) (998)) (literal (valuationOf q) (1002)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 2 (meaning998 q) (meaning1002 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1002 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_right (literal (valuationOf q) (999)) (literal (valuationOf q) (1003)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 3 (meaning999 q) (meaning1003 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1003 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_left (literal (valuationOf q) (990)) (literal (valuationOf q) (1001)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 1 (meaning990 q) (meaning1001 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1001 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1002)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 1 1 (meaning990 q) (meaning997 q) (meaning1002 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 997 = false ∨ valuation q 1002 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1003)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 1 2 (meaning990 q) (meaning998 q) (meaning1003 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 998 = false ∨ valuation q 1003 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1004)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 1 3 (meaning990 q) (meaning999 q) (meaning1004 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 999 = false ∨ valuation q 1004 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1005)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 1 4 (meaning990 q) (meaning1000 q) (meaning1005 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1000 = false ∨ valuation q 1005 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_left (literal (valuationOf q) (991)) (literal (valuationOf q) (1002)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 2 (meaning991 q) (meaning1002 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 1002 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1003)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 2 1 (meaning991 q) (meaning997 q) (meaning1003 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 997 = false ∨ valuation q 1003 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1004)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 2 2 (meaning991 q) (meaning998 q) (meaning1004 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 998 = false ∨ valuation q 1004 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1005)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 2 3 (meaning991 q) (meaning999 q) (meaning1005 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 999 = false ∨ valuation q 1005 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_left (literal (valuationOf q) (992)) (literal (valuationOf q) (1003)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 3 (meaning992 q) (meaning1003 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 1003 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1004)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 3 1 (meaning992 q) (meaning997 q) (meaning1004 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 997 = false ∨ valuation q 1004 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1005)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 3 2 (meaning992 q) (meaning998 q) (meaning1005 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 998 = false ∨ valuation q 1005 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true := by
  have hs : count1001 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1006)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73, -74]) (count1001 q) 3 3 (meaning992 q) (meaning999 q) (meaning1006 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 999 = false ∨ valuation q 1006 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1008)) (countLit q [-76]) (countLit q [-79]) (count1008 q) 1 (meaningNeg79 q) (meaning1008 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1008 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1008)) (countLit q [-76]) (countLit q [-79]) (count1008 q) 1 (meaningNeg76 q) (meaning1008 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1008 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1009)) (countLit q [-76]) (countLit q [-79]) (count1008 q) 1 1 (meaningNeg76 q) (meaningNeg79 q) (meaning1009 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 1009 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1010)) (countLit q [-81]) (countLit q [-82]) (count1010 q) 1 (meaningNeg82 q) (meaning1010 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1010 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1010)) (countLit q [-81]) (countLit q [-82]) (count1010 q) 1 (meaningNeg81 q) (meaning1010 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1010 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1011 = true := by
  have hs : count1010 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1011)) (countLit q [-81]) (countLit q [-82]) (count1010 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1011 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1011 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1010 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1010)) (literal (valuationOf q) (1012)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1012 q) 1 (meaning1010 q) (meaning1012 q) hs
  change valuationOf q 1010 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1010 = false ∨ valuation q 1012 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E260.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112260
