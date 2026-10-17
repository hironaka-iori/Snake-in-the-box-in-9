import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-58, -61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (countLit q [-58, -61]) (countLit q [-63, -66]) (count1418 q) 2 (meaning1417 q) (meaning1419 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-58, -61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-63, -66])
  have hm := merge_left (literal (valuationOf q) (1414)) (literal (valuationOf q) (1418)) (countLit q [-58, -61]) (countLit q [-63, -66]) (count1418 q) 1 (meaning1414 q) (meaning1418 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1418 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-58, -61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1419)) (countLit q [-58, -61]) (countLit q [-63, -66]) (count1418 q) 1 1 (meaning1414 q) (meaning1416 q) (meaning1419 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1416 = false ∨ valuation q 1419 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1420 = true := by
  have hs : count1418 q = (countLit q [-58, -61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1420)) (countLit q [-58, -61]) (countLit q [-63, -66]) (count1418 q) 1 2 (meaning1414 q) (meaning1417 q) (meaning1420 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1417 = false ∨ valuation q 1420 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-58, -61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-63, -66])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1419)) (countLit q [-58, -61]) (countLit q [-63, -66]) (count1418 q) 2 (meaning1415 q) (meaning1419 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1419 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1420 = true := by
  have hs : count1418 q = (countLit q [-58, -61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1420)) (countLit q [-58, -61]) (countLit q [-63, -66]) (count1418 q) 2 1 (meaning1415 q) (meaning1416 q) (meaning1420 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1416 = false ∨ valuation q 1420 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1411)) (literal (valuationOf q) (1422)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 1 (meaning1411 q) (meaning1422 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1422 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1423)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 1 1 (meaning1411 q) (meaning1418 q) (meaning1423 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1418 = false ∨ valuation q 1423 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1424)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 1 2 (meaning1411 q) (meaning1419 q) (meaning1424 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1419 = false ∨ valuation q 1424 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1412)) (literal (valuationOf q) (1423)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 2 (meaning1412 q) (meaning1423 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1423 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1412)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1424)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 2 1 (meaning1412 q) (meaning1418 q) (meaning1424 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1418 = false ∨ valuation q 1424 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1425 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1412)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1425)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 2 2 (meaning1412 q) (meaning1419 q) (meaning1425 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1419 = false ∨ valuation q 1425 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1426 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1412)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1426)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 2 3 (meaning1412 q) (meaning1420 q) (meaning1426 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1420 = false ∨ valuation q 1426 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1413)) (literal (valuationOf q) (1424)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 3 (meaning1413 q) (meaning1424 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1424 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1425 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1425)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 3 1 (meaning1413 q) (meaning1418 q) (meaning1425 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1418 = false ∨ valuation q 1425 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1426 = true := by
  have hs : count1422 q = (countLit q [-54, -55, -56]) + (countLit q [-58, -61, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56]) (l₂ := [-58, -61, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1426)) (countLit q [-54, -55, -56]) (countLit q [-58, -61, -63, -66]) (count1422 q) 3 2 (meaning1413 q) (meaning1419 q) (meaning1426 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1419 = false ∨ valuation q 1426 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1429)) (countLit q [-70]) (countLit q [-71]) (count1429 q) 1 (meaningNeg71 q) (meaning1429 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1429 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1429)) (countLit q [-70]) (countLit q [-71]) (count1429 q) 1 (meaningNeg70 q) (meaning1429 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1429 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1430 = true := by
  have hs : count1429 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1430)) (countLit q [-70]) (countLit q [-71]) (count1429 q) 1 1 (meaningNeg70 q) (meaningNeg71 q) (meaning1430 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 1430 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1431)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 1 (meaning1429 q) (meaning1431 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1431 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1432 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1432)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 2 (meaning1430 q) (meaning1432 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1432 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1431)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 1 (meaningNeg68 q) (meaning1431 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1431 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true := by
  have hs : count1431 q = (countLit q [-68]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1432)) (countLit q [-68]) (countLit q [-70, -71]) (count1431 q) 1 1 (meaningNeg68 q) (meaning1429 q) (meaning1432 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1429 = false ∨ valuation q 1432 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1434)) (countLit q [-74]) (countLit q [-75]) (count1434 q) 1 (meaningNeg75 q) (meaning1434 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1434 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1434)) (countLit q [-74]) (countLit q [-75]) (count1434 q) 1 (meaningNeg74 q) (meaning1434 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1434 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 75 = true ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (1435)) (countLit q [-74]) (countLit q [-75]) (count1434 q) 1 1 (meaningNeg74 q) (meaningNeg75 q) (meaning1435 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 75 = true ∨ valuation q 1435 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1436)) (countLit q [-78]) (countLit q [-80]) (count1436 q) 1 (meaningNeg80 q) (meaning1436 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1436 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1436)) (countLit q [-78]) (countLit q [-80]) (count1436 q) 1 (meaningNeg78 q) (meaning1436 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1436 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1437)) (countLit q [-78]) (countLit q [-80]) (count1436 q) 1 1 (meaningNeg78 q) (meaningNeg80 q) (meaning1437 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 80 = true ∨ valuation q 1437 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-74, -75]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1438)) (countLit q [-74, -75]) (countLit q [-78, -80]) (count1438 q) 1 (meaning1436 q) (meaning1438 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1438 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-74, -75]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1437)) (literal (valuationOf q) (1439)) (countLit q [-74, -75]) (countLit q [-78, -80]) (count1438 q) 2 (meaning1437 q) (meaning1439 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1439 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-74, -75]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1438)) (countLit q [-74, -75]) (countLit q [-78, -80]) (count1438 q) 1 (meaning1434 q) (meaning1438 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1438 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E090.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112090
