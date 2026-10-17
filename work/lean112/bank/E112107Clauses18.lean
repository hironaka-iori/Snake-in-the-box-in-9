import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1438)) (countLit q [-56]) (countLit q [-59, -60]) (count1438 q) 1 (meaning1436 q) (meaning1438 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1438 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (1437)) (literal (valuationOf q) (1439)) (countLit q [-56]) (countLit q [-59, -60]) (count1438 q) 2 (meaning1437 q) (meaning1439 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1439 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1438)) (countLit q [-56]) (countLit q [-59, -60]) (count1438 q) 1 (meaningNeg56 q) (meaning1438 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1438 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1439)) (countLit q [-56]) (countLit q [-59, -60]) (count1438 q) 1 1 (meaningNeg56 q) (meaning1436 q) (meaning1439 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1436 = false ∨ valuation q 1439 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1437 = false ∨ valuationOf q 1440 = true := by
  have hs : count1438 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1440)) (countLit q [-56]) (countLit q [-59, -60]) (count1438 q) 1 2 (meaningNeg56 q) (meaning1437 q) (meaning1440 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1437 = false ∨ valuation q 1440 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1441)) (countLit q [-66]) (countLit q [-67]) (count1441 q) 1 (meaningNeg67 q) (meaning1441 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1441 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1441)) (countLit q [-66]) (countLit q [-67]) (count1441 q) 1 (meaningNeg66 q) (meaning1441 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1441 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1442)) (countLit q [-66]) (countLit q [-67]) (count1441 q) 1 1 (meaningNeg66 q) (meaningNeg67 q) (meaning1442 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 1442 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-63]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-63]) (countLit q [-66, -67]) (count1443 q) 1 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-63]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (countLit q [-63]) (countLit q [-66, -67]) (count1443 q) 2 (meaning1442 q) (meaning1444 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-63]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66, -67])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1443)) (countLit q [-63]) (countLit q [-66, -67]) (count1443 q) 1 (meaningNeg63 q) (meaning1443 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1443 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-63]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66, -67])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1444)) (countLit q [-63]) (countLit q [-66, -67]) (count1443 q) 1 1 (meaningNeg63 q) (meaning1441 q) (meaning1444 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1441 = false ∨ valuation q 1444 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 1 (meaning1443 q) (meaning1446 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1446 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_right (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 2 (meaning1444 q) (meaning1447 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1447 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_left (literal (valuationOf q) (1438)) (literal (valuationOf q) (1446)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 1 (meaning1438 q) (meaning1446 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1446 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 1 1 (meaning1438 q) (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1443 = false ∨ valuation q 1447 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 1 2 (meaning1438 q) (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1444 = false ∨ valuation q 1448 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_left (literal (valuationOf q) (1439)) (literal (valuationOf q) (1447)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 2 (meaning1439 q) (meaning1447 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1447 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 2 1 (meaning1439 q) (meaning1443 q) (meaning1448 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1443 = false ∨ valuation q 1448 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-56, -59, -60]) + (countLit q [-63, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-63, -66, -67])
  have hm := merge_left (literal (valuationOf q) (1440)) (literal (valuationOf q) (1448)) (countLit q [-56, -59, -60]) (countLit q [-63, -66, -67]) (count1446 q) 3 (meaning1440 q) (meaning1448 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1448 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1452)) (countLit q [-73]) (countLit q [-74]) (count1452 q) 1 (meaningNeg74 q) (meaning1452 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1452 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1452)) (countLit q [-73]) (countLit q [-74]) (count1452 q) 1 (meaningNeg73 q) (meaning1452 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1452 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1453)) (countLit q [-73]) (countLit q [-74]) (count1452 q) 1 1 (meaningNeg73 q) (meaningNeg74 q) (meaning1453 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 1453 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-69]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1454)) (countLit q [-69]) (countLit q [-73, -74]) (count1454 q) 1 (meaning1452 q) (meaning1454 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1454 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-69]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1455)) (countLit q [-69]) (countLit q [-73, -74]) (count1454 q) 2 (meaning1453 q) (meaning1455 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1455 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-69]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73, -74])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1454)) (countLit q [-69]) (countLit q [-73, -74]) (count1454 q) 1 (meaningNeg69 q) (meaning1454 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1454 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1452 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-69]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1455)) (countLit q [-69]) (countLit q [-73, -74]) (count1454 q) 1 1 (meaningNeg69 q) (meaning1452 q) (meaning1455 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1452 = false ∨ valuation q 1455 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1453 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-69]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1456)) (countLit q [-69]) (countLit q [-73, -74]) (count1454 q) 1 2 (meaningNeg69 q) (meaning1453 q) (meaning1456 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1453 = false ∨ valuation q 1456 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1457)) (countLit q [-75]) (countLit q [-76]) (count1457 q) 1 (meaningNeg76 q) (meaning1457 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1457 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1457)) (countLit q [-75]) (countLit q [-76]) (count1457 q) 1 (meaningNeg75 q) (meaning1457 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1457 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1458)) (countLit q [-75]) (countLit q [-76]) (count1457 q) 1 1 (meaningNeg75 q) (meaningNeg76 q) (meaning1458 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 1458 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1459)) (countLit q [-79]) (countLit q [-82]) (count1459 q) 1 (meaningNeg82 q) (meaning1459 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1459 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E107.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112107
