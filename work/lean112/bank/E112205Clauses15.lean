import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1454)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 2 (meaning1441 q) (meaning1449 q) (meaning1454 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1449 = false ∨ valuation q 1454 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1455)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 3 (meaning1441 q) (meaning1450 q) (meaning1455 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1450 = false ∨ valuation q 1455 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1442)) (literal (valuationOf q) (1453)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 2 (meaning1442 q) (meaning1453 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1453 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1454)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 2 1 (meaning1442 q) (meaning1448 q) (meaning1454 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1448 = false ∨ valuation q 1454 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1455)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 2 2 (meaning1442 q) (meaning1449 q) (meaning1455 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1449 = false ∨ valuation q 1455 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 3 (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1454 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1455)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 3 1 (meaning1443 q) (meaning1448 q) (meaning1455 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1448 = false ∨ valuation q 1455 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1460)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 (meaning1453 q) (meaning1460 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1460 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1460)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 1 1 (meaning1433 q) (meaning1452 q) (meaning1460 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1452 = false ∨ valuation q 1460 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1461)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 1 2 (meaning1433 q) (meaning1453 q) (meaning1461 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1453 = false ∨ valuation q 1461 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1462)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 1 3 (meaning1433 q) (meaning1454 q) (meaning1462 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1454 = false ∨ valuation q 1462 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1463 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1463)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 1 4 (meaning1433 q) (meaning1455 q) (meaning1463 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1455 = false ∨ valuation q 1463 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1460)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 (meaning1434 q) (meaning1460 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1460 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1461)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 1 (meaning1434 q) (meaning1452 q) (meaning1461 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1452 = false ∨ valuation q 1461 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1462)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 2 (meaning1434 q) (meaning1453 q) (meaning1462 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1453 = false ∨ valuation q 1462 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1463 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1463)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 2 3 (meaning1434 q) (meaning1454 q) (meaning1463 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1454 = false ∨ valuation q 1463 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1435)) (literal (valuationOf q) (1461)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 3 (meaning1435 q) (meaning1461 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1461 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1462)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 3 1 (meaning1435 q) (meaning1452 q) (meaning1462 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1452 = false ∨ valuation q 1462 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true := by
  have hs : count1459 q = (countLit q [-59, -61, -63, -64, -66, -69]) + (countLit q [-71, -72, -74, -77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69]) (l₂ := [-71, -72, -74, -77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1463)) (countLit q [-59, -61, -63, -64, -66, -69]) (countLit q [-71, -72, -74, -77, -79, -80, -82]) (count1459 q) 3 2 (meaning1435 q) (meaning1453 q) (meaning1463 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1453 = false ∨ valuation q 1463 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1471)) (countLit q [-87]) (countLit q [-88]) (count1471 q) 1 (meaningNeg88 q) (meaning1471 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1471 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1471)) (countLit q [-87]) (countLit q [-88]) (count1471 q) 1 (meaningNeg87 q) (meaning1471 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1471 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1472)) (countLit q [-87]) (countLit q [-88]) (count1471 q) 1 1 (meaningNeg87 q) (meaningNeg88 q) (meaning1472 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 1472 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 (meaning1471 q) (meaning1473 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 2 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1473)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 (meaningNeg85 q) (meaning1473 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1473 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 1 (meaningNeg85 q) (meaning1471 q) (meaning1474 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1471 = false ∨ valuation q 1474 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1473 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-85]) (countLit q [-87, -88]) (count1473 q) 1 2 (meaningNeg85 q) (meaning1472 q) (meaning1475 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1476)) (countLit q [-94]) (countLit q [-97]) (count1476 q) 1 (meaningNeg97 q) (meaning1476 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1476 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1476)) (countLit q [-94]) (countLit q [-97]) (count1476 q) 1 (meaningNeg94 q) (meaning1476 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1476 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1477)) (countLit q [-94]) (countLit q [-97]) (count1476 q) 1 1 (meaningNeg94 q) (meaningNeg97 q) (meaning1477 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 97 = true ∨ valuation q 1477 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -97])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-91]) (countLit q [-94, -97]) (count1478 q) 1 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-91]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -97])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (countLit q [-91]) (countLit q [-94, -97]) (count1478 q) 2 (meaning1477 q) (meaning1479 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E205.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112205
