import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 1 1 (meaning1444 q) (meaning1446 q) (meaning1449 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = false ∨ valuation q 1449 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1450)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 1 2 (meaning1444 q) (meaning1447 q) (meaning1450 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1447 = false ∨ valuation q 1450 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1449)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 2 (meaning1445 q) (meaning1449 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1449 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 2 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 3 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1452)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 (meaning1441 q) (meaning1452 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1452 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 1 (meaning1441 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1454)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 2 (meaning1441 q) (meaning1449 q) (meaning1454 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1449 = false ∨ valuation q 1454 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1460)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 (meaning1453 q) (meaning1460 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1460 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1460)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 1 1 (meaning1433 q) (meaning1452 q) (meaning1460 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1452 = false ∨ valuation q 1460 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1461)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 1 2 (meaning1433 q) (meaning1453 q) (meaning1461 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1453 = false ∨ valuation q 1461 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1462)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 1 3 (meaning1433 q) (meaning1454 q) (meaning1462 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1454 = false ∨ valuation q 1462 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1460)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 (meaning1434 q) (meaning1460 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1460 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1461)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 1 (meaning1434 q) (meaning1452 q) (meaning1461 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1452 = false ∨ valuation q 1461 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1462)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 2 (meaning1434 q) (meaning1453 q) (meaning1462 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1453 = false ∨ valuation q 1462 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1471)) (countLit q [-87]) (countLit q [-88]) (count1471 q) 1 (meaningNeg88 q) (meaning1471 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1471 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1471)) (countLit q [-87]) (countLit q [-88]) (count1471 q) 1 (meaningNeg87 q) (meaning1471 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1471 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1472)) (countLit q [-87]) (countLit q [-88]) (count1471 q) 1 1 (meaningNeg87 q) (meaningNeg88 q) (meaning1472 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 1472 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 (meaning1471 q) (meaning1473 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1473)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 (meaningNeg85 q) (meaning1473 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1473 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 1 (meaningNeg85 q) (meaning1471 q) (meaning1474 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1471 = false ∨ valuation q 1474 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 2 (meaningNeg85 q) (meaning1472 q) (meaning1475 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1476)) (countLit q [-94]) (countLit q [-96]) (count1476 q) 1 (meaningNeg96 q) (meaning1476 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1476 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1476)) (countLit q [-94]) (countLit q [-96]) (count1476 q) 1 (meaningNeg94 q) (meaning1476 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1476 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1477)) (countLit q [-94]) (countLit q [-96]) (count1476 q) 1 1 (meaningNeg94 q) (meaningNeg96 q) (meaning1477 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 1477 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -96])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-91]) (countLit q [-94, -96]) (count1478 q) 1 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -96])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (countLit q [-91]) (countLit q [-94, -96]) (count1478 q) 2 (meaning1477 q) (meaning1479 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -96])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1478)) (countLit q [-91]) (countLit q [-94, -96]) (count1478 q) 1 (meaningNeg91 q) (meaning1478 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1478 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-91]) (countLit q [-94, -96]) (count1478 q) 1 1 (meaningNeg91 q) (meaning1476 q) (meaning1479 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (countLit q [-91]) (countLit q [-94, -96]) (count1478 q) 1 2 (meaningNeg91 q) (meaning1477 q) (meaning1480 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1477 = false ∨ valuation q 1480 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1481)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 1 (meaning1478 q) (meaning1481 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1481 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E201.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112201
