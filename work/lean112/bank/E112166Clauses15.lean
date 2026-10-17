import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1423)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 1 1 (meaning1411 q) (meaning1418 q) (meaning1423 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1418 = false ∨ valuation q 1423 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1424)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 1 2 (meaning1411 q) (meaning1419 q) (meaning1424 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1419 = false ∨ valuation q 1424 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1425 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1425)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 1 3 (meaning1411 q) (meaning1420 q) (meaning1425 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1420 = false ∨ valuation q 1425 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1412)) (literal (valuationOf q) (1423)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 2 (meaning1412 q) (meaning1423 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1423 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1412)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1424)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 2 1 (meaning1412 q) (meaning1418 q) (meaning1424 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1418 = false ∨ valuation q 1424 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1425 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1412)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1425)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 2 2 (meaning1412 q) (meaning1419 q) (meaning1425 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1419 = false ∨ valuation q 1425 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1426 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1412)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1426)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 2 3 (meaning1412 q) (meaning1420 q) (meaning1426 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1420 = false ∨ valuation q 1426 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1413)) (literal (valuationOf q) (1424)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 3 (meaning1413 q) (meaning1424 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1424 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1425 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1425)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 3 1 (meaning1413 q) (meaning1418 q) (meaning1425 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1418 = false ∨ valuation q 1425 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1426 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1426)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 3 2 (meaning1413 q) (meaning1419 q) (meaning1426 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1419 = false ∨ valuation q 1426 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1429)) (countLit q [-70]) (countLit q [-71]) (count1429 q) 1 (meaningNeg71 q) (meaning1429 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1429 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1429)) (countLit q [-70]) (countLit q [-71]) (count1429 q) 1 (meaningNeg70 q) (meaning1429 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1429 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1430 = true := by
  have hs : count1429 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1430)) (countLit q [-70]) (countLit q [-71]) (count1429 q) 1 1 (meaningNeg70 q) (meaningNeg71 q) (meaning1430 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 1430 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1431)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 1 (meaning1429 q) (meaning1431 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1431 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1432 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1432)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 2 (meaning1430 q) (meaning1432 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1432 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1431)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 1 (meaningNeg68 q) (meaning1431 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1431 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1432)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 1 1 (meaningNeg68 q) (meaning1429 q) (meaning1432 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1429 = false ∨ valuation q 1432 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1430 = false ∨ valuationOf q 1433 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1433)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 1 2 (meaningNeg68 q) (meaning1430 q) (meaning1433 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1430 = false ∨ valuation q 1433 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1434)) (countLit q [-73]) (countLit q [-74]) (count1434 q) 1 (meaningNeg74 q) (meaning1434 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1434 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1434)) (countLit q [-73]) (countLit q [-74]) (count1434 q) 1 (meaningNeg73 q) (meaning1434 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1434 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1435)) (countLit q [-73]) (countLit q [-74]) (count1434 q) 1 1 (meaningNeg73 q) (meaningNeg74 q) (meaning1435 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 1435 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1436)) (countLit q [-78]) (countLit q [-79]) (count1436 q) 1 (meaningNeg79 q) (meaning1436 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1436 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1436)) (countLit q [-78]) (countLit q [-79]) (count1436 q) 1 (meaningNeg78 q) (meaning1436 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1436 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-73, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1438)) (countLit q [-73, -74]) (countLit q [-78, -79]) (count1438 q) 1 (meaning1436 q) (meaning1438 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1438 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-73, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1438)) (countLit q [-73, -74]) (countLit q [-78, -79]) (count1438 q) 1 (meaning1434 q) (meaning1438 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1438 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-73, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1439)) (countLit q [-73, -74]) (countLit q [-78, -79]) (count1438 q) 1 1 (meaning1434 q) (meaning1436 q) (meaning1439 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1436 = false ∨ valuation q 1439 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-73, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (1435)) (literal (valuationOf q) (1439)) (countLit q [-73, -74]) (countLit q [-78, -79]) (count1438 q) 2 (meaning1435 q) (meaning1439 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1439 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1440 = true := by
  have hs : count1438 q = (countLit q [-73, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1440)) (countLit q [-73, -74]) (countLit q [-78, -79]) (count1438 q) 2 1 (meaning1435 q) (meaning1436 q) (meaning1440 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1436 = false ∨ valuation q 1440 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_right (literal (valuationOf q) (1438)) (literal (valuationOf q) (1442)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 1 (meaning1438 q) (meaning1442 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1442 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1443)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 2 (meaning1439 q) (meaning1443 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1443 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1444)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 3 (meaning1440 q) (meaning1444 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1444 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1431)) (literal (valuationOf q) (1442)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 1 (meaning1431 q) (meaning1442 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1442 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E166.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112166
