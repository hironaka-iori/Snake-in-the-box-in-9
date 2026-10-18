import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1460 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1460)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 3 2 (meaning1447 q) (meaning1453 q) (meaning1460 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1453 = false ∨ valuation q 1460 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1463)) (countLit q [-72]) (countLit q [-74]) (count1463 q) 1 (meaningNeg74 q) (meaning1463 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1463 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1463)) (countLit q [-72]) (countLit q [-74]) (count1463 q) 1 (meaningNeg72 q) (meaning1463 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1463 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1464)) (countLit q [-72]) (countLit q [-74]) (count1463 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning1464 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 1464 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-70]) (countLit q [-72, -74]) (count1465 q) 1 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-70]) (countLit q [-72, -74]) (count1465 q) 2 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -74])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1465)) (countLit q [-70]) (countLit q [-72, -74]) (count1465 q) 1 (meaningNeg70 q) (meaning1465 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1465 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-70]) (countLit q [-72, -74]) (count1465 q) 1 1 (meaningNeg70 q) (meaning1463 q) (meaning1466 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-70]) (countLit q [-72, -74]) (count1465 q) 1 2 (meaningNeg70 q) (meaning1464 q) (meaning1467 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1468)) (countLit q [-76]) (countLit q [-78]) (count1468 q) 1 (meaningNeg78 q) (meaning1468 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1468 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1468)) (countLit q [-76]) (countLit q [-78]) (count1468 q) 1 (meaningNeg76 q) (meaning1468 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1468 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1469)) (countLit q [-76]) (countLit q [-78]) (count1468 q) 1 1 (meaningNeg76 q) (meaningNeg78 q) (meaning1469 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 1469 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1470)) (countLit q [-80]) (countLit q [-81]) (count1470 q) 1 (meaningNeg81 q) (meaning1470 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1470 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1470)) (countLit q [-80]) (countLit q [-81]) (count1470 q) 1 (meaningNeg80 q) (meaning1470 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1470 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1471)) (countLit q [-80]) (countLit q [-81]) (count1470 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1471 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1471 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 1 (meaning1470 q) (meaning1472 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 2 (meaning1471 q) (meaning1473 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1472)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 1 (meaning1468 q) (meaning1472 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1472 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1473)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 1 1 (meaning1468 q) (meaning1470 q) (meaning1473 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1470 = false ∨ valuation q 1473 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 1 2 (meaning1468 q) (meaning1471 q) (meaning1474 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1471 = false ∨ valuation q 1474 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1473)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 2 (meaning1469 q) (meaning1473 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1473 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 2 1 (meaning1469 q) (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1470 = false ∨ valuation q 1474 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1472 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count1472 q) 2 2 (meaning1469 q) (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1471 = false ∨ valuation q 1475 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 1 (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 3 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_left (literal (valuationOf q) (1465)) (literal (valuationOf q) (1476)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 1 (meaning1465 q) (meaning1476 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1476 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1477)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 1 1 (meaning1465 q) (meaning1472 q) (meaning1477 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1472 = false ∨ valuation q 1477 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 1 2 (meaning1465 q) (meaning1473 q) (meaning1478 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1473 = false ∨ valuation q 1478 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 1 3 (meaning1465 q) (meaning1474 q) (meaning1479 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1474 = false ∨ valuation q 1479 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1480)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 1 4 (meaning1465 q) (meaning1475 q) (meaning1480 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1475 = false ∨ valuation q 1480 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_left (literal (valuationOf q) (1466)) (literal (valuationOf q) (1477)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 2 (meaning1466 q) (meaning1477 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1477 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-70, -72, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-70, -72, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1478)) (countLit q [-70, -72, -74]) (countLit q [-76, -78, -80, -81]) (count1476 q) 2 1 (meaning1466 q) (meaning1472 q) (meaning1478 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1472 = false ∨ valuation q 1478 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E161.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112161
