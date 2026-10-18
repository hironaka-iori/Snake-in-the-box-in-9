import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1418 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 5 3 (meaning1355 q) (meaning1401 q) (meaning1418 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1401 = false ∨ valuation q 1418 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1419 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 5 4 (meaning1355 q) (meaning1402 q) (meaning1419 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1402 = false ∨ valuation q 1419 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1419 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 7 2 (meaning1357 q) (meaning1400 q) (meaning1419 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1400 = false ∨ valuation q 1419 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1423)) (countLit q [-61]) (countLit q [-63]) (count1423 q) 1 (meaningNeg63 q) (meaning1423 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1423 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1423)) (countLit q [-61]) (countLit q [-63]) (count1423 q) 1 (meaningNeg61 q) (meaning1423 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1423 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1424)) (countLit q [-61]) (countLit q [-63]) (count1423 q) 1 1 (meaningNeg61 q) (meaningNeg63 q) (meaning1424 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 1424 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1425)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 1 (meaning1423 q) (meaning1425 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1425 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1424)) (literal (valuationOf q) (1426)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 2 (meaning1424 q) (meaning1426 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1426 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1425)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 1 (meaningNeg59 q) (meaning1425 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1425 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1426)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 1 1 (meaningNeg59 q) (meaning1423 q) (meaning1426 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1423 = false ∨ valuation q 1426 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-66]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1428)) (countLit q [-66]) (countLit q [-69]) (count1428 q) 1 (meaningNeg69 q) (meaning1428 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1428 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-66]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1428)) (countLit q [-66]) (countLit q [-69]) (count1428 q) 1 (meaningNeg66 q) (meaning1428 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1428 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-64]) + (countLit q [-66, -69]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -69])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (countLit q [-64]) (countLit q [-66, -69]) (count1430 q) 1 (meaning1428 q) (meaning1430 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-64]) + (countLit q [-66, -69]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -69])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1430)) (countLit q [-64]) (countLit q [-66, -69]) (count1430 q) 1 (meaningNeg64 q) (meaning1430 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1430 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-64]) + (countLit q [-66, -69]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -69])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (countLit q [-64]) (countLit q [-66, -69]) (count1430 q) 1 1 (meaningNeg64 q) (meaning1428 q) (meaning1431 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1428 = false ∨ valuation q 1431 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1433)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 1 (meaning1430 q) (meaning1433 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1433 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1434)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 2 (meaning1431 q) (meaning1434 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1434 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1433)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 1 (meaning1425 q) (meaning1433 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1433 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 1 1 (meaning1425 q) (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1430 = false ∨ valuation q 1434 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1434)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 2 (meaning1426 q) (meaning1434 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1434 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1439)) (countLit q [-72]) (countLit q [-74]) (count1439 q) 1 (meaningNeg74 q) (meaning1439 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1439 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1439)) (countLit q [-72]) (countLit q [-74]) (count1439 q) 1 (meaningNeg72 q) (meaning1439 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1439 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1441)) (countLit q [-71]) (countLit q [-72, -74]) (count1441 q) 1 (meaning1439 q) (meaning1441 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1441 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72, -74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1441)) (countLit q [-71]) (countLit q [-72, -74]) (count1441 q) 1 (meaningNeg71 q) (meaning1441 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1441 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1444)) (countLit q [-77]) (countLit q [-79]) (count1444 q) 1 (meaningNeg79 q) (meaning1444 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1444 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1444)) (countLit q [-77]) (countLit q [-79]) (count1444 q) 1 (meaningNeg77 q) (meaning1444 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1444 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1445)) (countLit q [-77]) (countLit q [-79]) (count1444 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1445 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1445 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1446)) (countLit q [-80]) (countLit q [-82]) (count1446 q) 1 (meaningNeg82 q) (meaning1446 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1446 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1446)) (countLit q [-80]) (countLit q [-82]) (count1446 q) 1 (meaningNeg80 q) (meaning1446 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1446 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1447)) (countLit q [-80]) (countLit q [-82]) (count1446 q) 1 1 (meaningNeg80 q) (meaningNeg82 q) (meaning1447 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 1447 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 1 (meaning1446 q) (meaning1448 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 1 (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1448 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E201.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112201
