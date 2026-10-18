import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1443)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 1 1 (meaning1431 q) (meaning1438 q) (meaning1443 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1438 = false ∨ valuation q 1443 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1444)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 1 2 (meaning1431 q) (meaning1439 q) (meaning1444 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1439 = false ∨ valuation q 1444 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1445)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 1 3 (meaning1431 q) (meaning1440 q) (meaning1445 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1440 = false ∨ valuation q 1445 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1432)) (literal (valuationOf q) (1443)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 2 (meaning1432 q) (meaning1443 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1443 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1444)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 2 1 (meaning1432 q) (meaning1438 q) (meaning1444 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1438 = false ∨ valuation q 1444 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1445 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1445)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 2 2 (meaning1432 q) (meaning1439 q) (meaning1445 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1439 = false ∨ valuation q 1445 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1433)) (literal (valuationOf q) (1444)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 3 (meaning1433 q) (meaning1444 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1444 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1445 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1445)) (countLit q [-68, -70, -71]) (countLit q [-73, -74, -78, -79]) (count1442 q) 3 1 (meaning1433 q) (meaning1438 q) (meaning1445 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1438 = false ∨ valuation q 1445 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1450)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 1 1 (meaning1422 q) (meaning1442 q) (meaning1450 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1442 = false ∨ valuation q 1450 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 1 2 (meaning1422 q) (meaning1443 q) (meaning1451 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1443 = false ∨ valuation q 1451 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1452)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 1 3 (meaning1422 q) (meaning1444 q) (meaning1452 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1444 = false ∨ valuation q 1452 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 1 4 (meaning1422 q) (meaning1445 q) (meaning1453 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1445 = false ∨ valuation q 1453 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1450)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 2 (meaning1423 q) (meaning1450 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1450 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1451)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 2 1 (meaning1423 q) (meaning1442 q) (meaning1451 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1442 = false ∨ valuation q 1451 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1452)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 2 2 (meaning1423 q) (meaning1443 q) (meaning1452 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1443 = false ∨ valuation q 1452 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1453)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 2 3 (meaning1423 q) (meaning1444 q) (meaning1453 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1444 = false ∨ valuation q 1453 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 2 4 (meaning1423 q) (meaning1445 q) (meaning1454 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1445 = false ∨ valuation q 1454 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1451)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 3 (meaning1424 q) (meaning1451 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1451 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1452)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 3 1 (meaning1424 q) (meaning1442 q) (meaning1452 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1442 = false ∨ valuation q 1452 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1453)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 3 2 (meaning1424 q) (meaning1443 q) (meaning1453 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1443 = false ∨ valuation q 1453 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1454)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 3 3 (meaning1424 q) (meaning1444 q) (meaning1454 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1444 = false ∨ valuation q 1454 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1452)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 4 (meaning1425 q) (meaning1452 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1452 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1453)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 4 1 (meaning1425 q) (meaning1442 q) (meaning1453 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1442 = false ∨ valuation q 1453 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 4 2 (meaning1425 q) (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1443 = false ∨ valuation q 1454 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1454)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 5 1 (meaning1426 q) (meaning1442 q) (meaning1454 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1442 = false ∨ valuation q 1454 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1455 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1455)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 5 2 (meaning1426 q) (meaning1443 q) (meaning1455 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1443 = false ∨ valuation q 1455 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1456 = true := by
  have hs : count1449 q = (countLit q [-53, -56, -58, -59, -62, -63, -66]) + (countLit q [-68, -70, -71, -73, -74, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66]) (l₂ := [-68, -70, -71, -73, -74, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1456)) (countLit q [-53, -56, -58, -59, -62, -63, -66]) (countLit q [-68, -70, -71, -73, -74, -78, -79]) (count1449 q) 5 3 (meaning1426 q) (meaning1444 q) (meaning1456 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1444 = false ∨ valuation q 1456 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1463)) (countLit q [-84]) (countLit q [-86]) (count1463 q) 1 (meaningNeg86 q) (meaning1463 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1463 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1463)) (countLit q [-84]) (countLit q [-86]) (count1463 q) 1 (meaningNeg84 q) (meaning1463 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1463 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1464)) (countLit q [-84]) (countLit q [-86]) (count1463 q) 1 1 (meaningNeg84 q) (meaningNeg86 q) (meaning1464 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 1464 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-81]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84, -86])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-81]) (countLit q [-84, -86]) (count1465 q) 1 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-81]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84, -86])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-81]) (countLit q [-84, -86]) (count1465 q) 2 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E166.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112166
