import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1005)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 3 2 (meaning992 q) (meaning998 q) (meaning1005 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 998 = false ∨ valuation q 1005 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1006)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 3 3 (meaning992 q) (meaning999 q) (meaning1006 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 999 = false ∨ valuation q 1006 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1007 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1007)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 3 4 (meaning992 q) (meaning1000 q) (meaning1007 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 1000 = false ∨ valuation q 1007 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1008)) (countLit q [-76]) (countLit q [-78]) (count1008 q) 1 (meaningNeg78 q) (meaning1008 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1008 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1008)) (countLit q [-76]) (countLit q [-78]) (count1008 q) 1 (meaningNeg76 q) (meaning1008 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1008 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1009)) (countLit q [-76]) (countLit q [-78]) (count1008 q) 1 1 (meaningNeg76 q) (meaningNeg78 q) (meaning1009 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 1009 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-79]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1010)) (countLit q [-79]) (countLit q [-83]) (count1010 q) 1 (meaningNeg83 q) (meaning1010 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1010 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-79]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1010)) (countLit q [-79]) (countLit q [-83]) (count1010 q) 1 (meaningNeg79 q) (meaning1010 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1010 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 83 = true ∨ valuationOf q 1011 = true := by
  have hs : count1010 q = (countLit q [-79]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-83)) (literal (valuationOf q) (1011)) (countLit q [-79]) (countLit q [-83]) (count1010 q) 1 1 (meaningNeg79 q) (meaningNeg83 q) (meaning1011 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 83)) = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 1011 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1010 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_right (literal (valuationOf q) (1010)) (literal (valuationOf q) (1012)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 1 (meaning1010 q) (meaning1012 q) hs
  change valuationOf q 1010 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1010 = false ∨ valuation q 1012 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1011 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_right (literal (valuationOf q) (1011)) (literal (valuationOf q) (1013)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 2 (meaning1011 q) (meaning1013 q) hs
  change valuationOf q 1011 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1011 = false ∨ valuation q 1013 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_left (literal (valuationOf q) (1008)) (literal (valuationOf q) (1012)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 1 (meaning1008 q) (meaning1012 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1012 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1013)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 1 1 (meaning1008 q) (meaning1010 q) (meaning1013 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1010 = false ∨ valuation q 1013 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1014)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 1 2 (meaning1008 q) (meaning1011 q) (meaning1014 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1011 = false ∨ valuation q 1014 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_left (literal (valuationOf q) (1009)) (literal (valuationOf q) (1013)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 2 (meaning1009 q) (meaning1013 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1013 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1014 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_two (literal (valuationOf q) (1009)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1014)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 2 1 (meaning1009 q) (meaning1010 q) (meaning1014 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1010 = false ∨ valuation q 1014 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1015 = true := by
  have hs : count1012 q = (countLit q [-76, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-79, -83])
  have hm := merge_two (literal (valuationOf q) (1009)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1015)) (countLit q [-76, -78]) (countLit q [-79, -83]) (count1012 q) 2 2 (meaning1009 q) (meaning1011 q) (meaning1015 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1015 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1011 = false ∨ valuation q 1015 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-84]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1016)) (countLit q [-84]) (countLit q [-88]) (count1016 q) 1 (meaningNeg88 q) (meaning1016 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1016 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-84]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1016)) (countLit q [-84]) (countLit q [-88]) (count1016 q) 1 (meaningNeg84 q) (meaning1016 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1016 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-84]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1017)) (countLit q [-84]) (countLit q [-88]) (count1016 q) 1 1 (meaningNeg84 q) (meaningNeg88 q) (meaning1017 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 1017 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1018)) (countLit q [-90]) (countLit q [-91]) (count1018 q) 1 (meaningNeg91 q) (meaning1018 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1018 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1018)) (countLit q [-90]) (countLit q [-91]) (count1018 q) 1 (meaningNeg90 q) (meaning1018 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1018 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1019 = true := by
  have hs : count1018 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1019)) (countLit q [-90]) (countLit q [-91]) (count1018 q) 1 1 (meaningNeg90 q) (meaningNeg91 q) (meaning1019 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 91 = true ∨ valuation q 1019 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_right (literal (valuationOf q) (1018)) (literal (valuationOf q) (1020)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 1 (meaning1018 q) (meaning1020 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1020 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_right (literal (valuationOf q) (1019)) (literal (valuationOf q) (1021)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 2 (meaning1019 q) (meaning1021 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1021 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_left (literal (valuationOf q) (1016)) (literal (valuationOf q) (1020)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 1 (meaning1016 q) (meaning1020 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1020 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1021)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 1 1 (meaning1016 q) (meaning1018 q) (meaning1021 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1018 = false ∨ valuation q 1021 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1022)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 1 2 (meaning1016 q) (meaning1019 q) (meaning1022 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1019 = false ∨ valuation q 1022 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_left (literal (valuationOf q) (1017)) (literal (valuationOf q) (1021)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 2 (meaning1017 q) (meaning1021 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1021 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1022 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1022)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 2 1 (meaning1017 q) (meaning1018 q) (meaning1022 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1018 = false ∨ valuation q 1022 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true := by
  have hs : count1020 q = (countLit q [-84, -88]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -88]) (l₂ := [-90, -91])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1023)) (countLit q [-84, -88]) (countLit q [-90, -91]) (count1020 q) 2 2 (meaning1017 q) (meaning1019 q) (meaning1023 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1019 = false ∨ valuation q 1023 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1020)) (literal (valuationOf q) (1024)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 1 (meaning1020 q) (meaning1024 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1024 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E256.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112256
