import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -97])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1478)) (countLit q [-91]) (countLit q [-94, -97]) (count1478 q) 1 (meaningNeg91 q) (meaning1478 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1478 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -97])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-91]) (countLit q [-94, -97]) (count1478 q) 1 1 (meaningNeg91 q) (meaning1476 q) (meaning1479 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -97])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (countLit q [-91]) (countLit q [-94, -97]) (count1478 q) 1 2 (meaningNeg91 q) (meaning1477 q) (meaning1480 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1477 = false ∨ valuation q 1480 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1481)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 1 (meaning1478 q) (meaning1481 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1481 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1482)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 2 (meaning1479 q) (meaning1482 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1482 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 3 (meaning1480 q) (meaning1483 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1483 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_left (literal (valuationOf q) (1473)) (literal (valuationOf q) (1481)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 1 (meaning1473 q) (meaning1481 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1481 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 1 1 (meaning1473 q) (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1478 = false ∨ valuation q 1482 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 1 2 (meaning1473 q) (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1479 = false ∨ valuation q 1483 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 1 3 (meaning1473 q) (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1480 = false ∨ valuation q 1484 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_left (literal (valuationOf q) (1474)) (literal (valuationOf q) (1482)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 2 (meaning1474 q) (meaning1482 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1482 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1483)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 2 1 (meaning1474 q) (meaning1478 q) (meaning1483 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = false ∨ valuation q 1483 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 2 2 (meaning1474 q) (meaning1479 q) (meaning1484 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1479 = false ∨ valuation q 1484 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -97]) (count1481 q) 3 1 (meaning1475 q) (meaning1478 q) (meaning1484 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1478 = false ∨ valuation q 1484 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1487)) (countLit q [-99]) (countLit q [-101]) (count1487 q) 1 (meaningNeg101 q) (meaning1487 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1487 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1487)) (countLit q [-99]) (countLit q [-101]) (count1487 q) 1 (meaningNeg99 q) (meaning1487 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1487 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1488)) (countLit q [-99]) (countLit q [-101]) (count1487 q) 1 1 (meaningNeg99 q) (meaningNeg101 q) (meaning1488 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 1488 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1487)) (literal (valuationOf q) (1489)) (countLit q [-98]) (countLit q [-99, -101]) (count1489 q) 1 (meaning1487 q) (meaning1489 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1489 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1488)) (literal (valuationOf q) (1490)) (countLit q [-98]) (countLit q [-99, -101]) (count1489 q) 2 (meaning1488 q) (meaning1490 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1490 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1489)) (countLit q [-98]) (countLit q [-99, -101]) (count1489 q) 1 (meaningNeg98 q) (meaning1489 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1489 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1490)) (countLit q [-98]) (countLit q [-99, -101]) (count1489 q) 1 1 (meaningNeg98 q) (meaning1487 q) (meaning1490 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1487 = false ∨ valuation q 1490 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1488 = false ∨ valuationOf q 1491 = true := by
  have hs : count1489 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1491)) (countLit q [-98]) (countLit q [-99, -101]) (count1489 q) 1 2 (meaningNeg98 q) (meaning1488 q) (meaning1491 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1488 = false ∨ valuation q 1491 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1492)) (countLit q [-104]) (countLit q [-105]) (count1492 q) 1 (meaningNeg105 q) (meaning1492 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1492 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1492)) (countLit q [-104]) (countLit q [-105]) (count1492 q) 1 (meaningNeg104 q) (meaning1492 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1492 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1493)) (countLit q [-104]) (countLit q [-105]) (count1492 q) 1 1 (meaningNeg104 q) (meaningNeg105 q) (meaning1493 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 1493 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1494)) (countLit q [-106]) (countLit q [-107]) (count1494 q) 1 (meaningNeg107 q) (meaning1494 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1494 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1494)) (countLit q [-106]) (countLit q [-107]) (count1494 q) 1 (meaningNeg106 q) (meaning1494 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1494 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1495)) (countLit q [-106]) (countLit q [-107]) (count1494 q) 1 1 (meaningNeg106 q) (meaningNeg107 q) (meaning1495 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 1495 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-104, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1496)) (countLit q [-104, -105]) (countLit q [-106, -107]) (count1496 q) 1 (meaning1494 q) (meaning1496 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1496 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-104, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (countLit q [-104, -105]) (countLit q [-106, -107]) (count1496 q) 2 (meaning1495 q) (meaning1497 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-104, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-104, -105]) (countLit q [-106, -107]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-104, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1497)) (countLit q [-104, -105]) (countLit q [-106, -107]) (count1496 q) 1 1 (meaning1492 q) (meaning1494 q) (meaning1497 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = false ∨ valuation q 1497 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E205.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112205
