import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-64]) + (countLit q [-66, -69]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -69])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (countLit q [-64]) (countLit q [-66, -69]) (count1430 q) 1 1 (meaningNeg64 q) (meaning1428 q) (meaning1431 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1428 = false ∨ valuation q 1431 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1433)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 1 (meaning1430 q) (meaning1433 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1433 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1434)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 2 (meaning1431 q) (meaning1434 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1434 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1433)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 1 (meaning1425 q) (meaning1433 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1433 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 1 1 (meaning1425 q) (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1430 = false ∨ valuation q 1434 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1435 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1435)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 1 2 (meaning1425 q) (meaning1431 q) (meaning1435 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1431 = false ∨ valuation q 1435 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1434)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 2 (meaning1426 q) (meaning1434 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1434 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true := by
  have hs : count1433 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1435)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69]) (count1433 q) 2 1 (meaning1426 q) (meaning1430 q) (meaning1435 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1430 = false ∨ valuation q 1435 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1439)) (countLit q [-72]) (countLit q [-74]) (count1439 q) 1 (meaningNeg74 q) (meaning1439 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1439 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1439)) (countLit q [-72]) (countLit q [-74]) (count1439 q) 1 (meaningNeg72 q) (meaning1439 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1439 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1440)) (countLit q [-72]) (countLit q [-74]) (count1439 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning1440 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 1440 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1441)) (countLit q [-71]) (countLit q [-72, -74]) (count1441 q) 1 (meaning1439 q) (meaning1441 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1441 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1442)) (countLit q [-71]) (countLit q [-72, -74]) (count1441 q) 2 (meaning1440 q) (meaning1442 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1442 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72, -74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1441)) (countLit q [-71]) (countLit q [-72, -74]) (count1441 q) 1 (meaningNeg71 q) (meaning1441 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1441 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1442)) (countLit q [-71]) (countLit q [-72, -74]) (count1441 q) 1 1 (meaningNeg71 q) (meaning1439 q) (meaning1442 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1439 = false ∨ valuation q 1442 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1443)) (countLit q [-71]) (countLit q [-72, -74]) (count1441 q) 1 2 (meaningNeg71 q) (meaning1440 q) (meaning1443 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1440 = false ∨ valuation q 1443 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1444)) (countLit q [-77]) (countLit q [-79]) (count1444 q) 1 (meaningNeg79 q) (meaning1444 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1444 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1444)) (countLit q [-77]) (countLit q [-79]) (count1444 q) 1 (meaningNeg77 q) (meaning1444 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1444 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1445)) (countLit q [-77]) (countLit q [-79]) (count1444 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1445 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1445 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1446)) (countLit q [-80]) (countLit q [-82]) (count1446 q) 1 (meaningNeg82 q) (meaning1446 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1446 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1446)) (countLit q [-80]) (countLit q [-82]) (count1446 q) 1 (meaningNeg80 q) (meaning1446 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1446 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1447)) (countLit q [-80]) (countLit q [-82]) (count1446 q) 1 1 (meaningNeg80 q) (meaningNeg82 q) (meaning1447 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 1447 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 1 (meaning1446 q) (meaning1448 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 2 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 1 (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1448 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 1 1 (meaning1444 q) (meaning1446 q) (meaning1449 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = false ∨ valuation q 1449 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1449)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 2 (meaning1445 q) (meaning1449 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1449 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1448 q = (countLit q [-77, -79]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-77, -79]) (countLit q [-80, -82]) (count1448 q) 2 1 (meaning1445 q) (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1446 = false ∨ valuation q 1450 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 2 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1452)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 (meaning1441 q) (meaning1452 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1452 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-71, -72, -74]) + (countLit q [-77, -79, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -72, -74]) (l₂ := [-77, -79, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-71, -72, -74]) (countLit q [-77, -79, -80, -82]) (count1452 q) 1 1 (meaning1441 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E205.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112205
