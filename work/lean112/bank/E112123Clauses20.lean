import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-31, -34, -35, -37, -38, -40]) + (countLit q [-43, -44, -46, -49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -38, -40]) (l₂ := [-43, -44, -46, -49, -52, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1411)) (countLit q [-31, -34, -35, -37, -38, -40]) (countLit q [-43, -44, -46, -49, -52, -53, -54]) (count1410 q) 1 1 (meaning1384 q) (meaning1403 q) (meaning1411 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1403 = false ∨ valuation q 1411 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-31, -34, -35, -37, -38, -40]) + (countLit q [-43, -44, -46, -49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -38, -40]) (l₂ := [-43, -44, -46, -49, -52, -53, -54])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1411)) (countLit q [-31, -34, -35, -37, -38, -40]) (countLit q [-43, -44, -46, -49, -52, -53, -54]) (count1410 q) 2 (meaning1385 q) (meaning1411 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1411 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) + (countLit q [-31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) (l₂ := [-31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1428)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) (countLit q [-31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) (count1423 q) 4 2 (meaning1364 q) (meaning1411 q) (meaning1428 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1411 = false ∨ valuation q 1428 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) + (countLit q [-31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) (l₂ := [-31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1429)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) (countLit q [-31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) (count1423 q) 5 2 (meaning1365 q) (meaning1411 q) (meaning1429 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1411 = false ∨ valuation q 1429 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1441)) (countLit q [-64]) (countLit q [-66]) (count1441 q) 1 (meaningNeg64 q) (meaning1441 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1441 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1442)) (countLit q [-64]) (countLit q [-66]) (count1441 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1442 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1442 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-61]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-61]) (countLit q [-64, -66]) (count1443 q) 1 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-61]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (countLit q [-61]) (countLit q [-64, -66]) (count1443 q) 2 (meaning1442 q) (meaning1444 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-56, -58, -59]) + (countLit q [-61, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-61, -64, -66])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-56, -58, -59]) (countLit q [-61, -64, -66]) (count1446 q) 1 (meaning1443 q) (meaning1446 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1446 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-56, -58, -59]) + (countLit q [-61, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-61, -64, -66])
  have hm := merge_right (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (countLit q [-56, -58, -59]) (countLit q [-61, -64, -66]) (count1446 q) 2 (meaning1444 q) (meaning1447 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1447 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1452)) (countLit q [-69]) (countLit q [-72]) (count1452 q) 1 (meaningNeg72 q) (meaning1452 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1452 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1452)) (countLit q [-69]) (countLit q [-72]) (count1452 q) 1 (meaningNeg69 q) (meaning1452 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1452 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1453)) (countLit q [-69]) (countLit q [-72]) (count1452 q) 1 1 (meaningNeg69 q) (meaningNeg72 q) (meaning1453 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 1453 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -72])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1454)) (countLit q [-67]) (countLit q [-69, -72]) (count1454 q) 1 (meaning1452 q) (meaning1454 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1454 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -72])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1455)) (countLit q [-67]) (countLit q [-69, -72]) (count1454 q) 2 (meaning1453 q) (meaning1455 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1455 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1457)) (countLit q [-74]) (countLit q [-75]) (count1457 q) 1 (meaningNeg75 q) (meaning1457 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1457 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1457)) (countLit q [-74]) (countLit q [-75]) (count1457 q) 1 (meaningNeg74 q) (meaning1457 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1457 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 75 = true ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (1458)) (countLit q [-74]) (countLit q [-75]) (count1457 q) 1 1 (meaningNeg74 q) (meaningNeg75 q) (meaning1458 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 75 = true ∨ valuation q 1458 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1459)) (countLit q [-78]) (countLit q [-82]) (count1459 q) 1 (meaningNeg78 q) (meaning1459 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1459 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-74, -75]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -82])
  have hm := merge_left (literal (valuationOf q) (1457)) (literal (valuationOf q) (1461)) (countLit q [-74, -75]) (countLit q [-78, -82]) (count1461 q) 1 (meaning1457 q) (meaning1461 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1461 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1463 = true := by
  have hs : count1461 q = (countLit q [-74, -75]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -82])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1459)) (literal (valuationOf q) (1463)) (countLit q [-74, -75]) (countLit q [-78, -82]) (count1461 q) 2 1 (meaning1458 q) (meaning1459 q) (meaning1463 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1459 = false ∨ valuation q 1463 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-67, -69, -72]) + (countLit q [-74, -75, -78, -82]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -72]) (l₂ := [-74, -75, -78, -82])
  have hm := merge_right (literal (valuationOf q) (1461)) (literal (valuationOf q) (1465)) (countLit q [-67, -69, -72]) (countLit q [-74, -75, -78, -82]) (count1465 q) 1 (meaning1461 q) (meaning1465 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1465 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-67, -69, -72]) + (countLit q [-74, -75, -78, -82]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -72]) (l₂ := [-74, -75, -78, -82])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-67, -69, -72]) (countLit q [-74, -75, -78, -82]) (count1465 q) 3 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-67, -69, -72]) + (countLit q [-74, -75, -78, -82]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -72]) (l₂ := [-74, -75, -78, -82])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1466)) (countLit q [-67, -69, -72]) (countLit q [-74, -75, -78, -82]) (count1465 q) 1 1 (meaning1454 q) (meaning1461 q) (meaning1466 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1461 = false ∨ valuation q 1466 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-67, -69, -72]) + (countLit q [-74, -75, -78, -82]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -72]) (l₂ := [-74, -75, -78, -82])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1467)) (countLit q [-67, -69, -72]) (countLit q [-74, -75, -78, -82]) (count1465 q) 2 1 (meaning1455 q) (meaning1461 q) (meaning1467 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1461 = false ∨ valuation q 1467 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-56, -58, -59, -61, -64, -66]) + (countLit q [-67, -69, -72, -74, -75, -78, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -61, -64, -66]) (l₂ := [-67, -69, -72, -74, -75, -78, -82])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1474)) (countLit q [-56, -58, -59, -61, -64, -66]) (countLit q [-67, -69, -72, -74, -75, -78, -82]) (count1472 q) 1 2 (meaning1446 q) (meaning1466 q) (meaning1474 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1466 = false ∨ valuation q 1474 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1475 = true := by
  have hs : count1472 q = (countLit q [-56, -58, -59, -61, -64, -66]) + (countLit q [-67, -69, -72, -74, -75, -78, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -61, -64, -66]) (l₂ := [-67, -69, -72, -74, -75, -78, -82])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1475)) (countLit q [-56, -58, -59, -61, -64, -66]) (countLit q [-67, -69, -72, -74, -75, -78, -82]) (count1472 q) 1 3 (meaning1446 q) (meaning1467 q) (meaning1475 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1467 = false ∨ valuation q 1475 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-56, -58, -59, -61, -64, -66]) + (countLit q [-67, -69, -72, -74, -75, -78, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -61, -64, -66]) (l₂ := [-67, -69, -72, -74, -75, -78, -82])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (countLit q [-56, -58, -59, -61, -64, -66]) (countLit q [-67, -69, -72, -74, -75, -78, -82]) (count1472 q) 2 1 (meaning1447 q) (meaning1465 q) (meaning1474 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1465 = false ∨ valuation q 1474 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1485)) (countLit q [-85]) (countLit q [-86]) (count1485 q) 1 (meaningNeg86 q) (meaning1485 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1485 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1485)) (countLit q [-85]) (countLit q [-86]) (count1485 q) 1 (meaningNeg85 q) (meaning1485 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1485 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1486)) (countLit q [-85]) (countLit q [-86]) (count1485 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1486 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1486 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1485)) (literal (valuationOf q) (1487)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 1 (meaning1485 q) (meaning1487 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1487 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E123.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112123
