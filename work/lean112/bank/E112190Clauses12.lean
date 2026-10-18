import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 2 1 (meaning1472 q) (meaning1478 q) (meaning1484 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1478 = false ∨ valuation q 1484 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1485 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1485)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 2 2 (meaning1472 q) (meaning1479 q) (meaning1485 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1479 = false ∨ valuation q 1485 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1485 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1485)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 3 1 (meaning1473 q) (meaning1478 q) (meaning1485 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1478 = false ∨ valuation q 1485 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1491 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1491)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 3 (meaning1484 q) (meaning1491 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1491 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1491 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1491)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 1 2 (meaning1462 q) (meaning1483 q) (meaning1491 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1483 = false ∨ valuation q 1491 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1492 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1492)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 1 3 (meaning1462 q) (meaning1484 q) (meaning1492 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1484 = false ∨ valuation q 1492 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1493 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1493)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 1 4 (meaning1462 q) (meaning1485 q) (meaning1493 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1485 = false ∨ valuation q 1493 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 2 1 (meaning1463 q) (meaning1482 q) (meaning1491 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1482 = false ∨ valuation q 1491 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1492)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 2 2 (meaning1463 q) (meaning1483 q) (meaning1492 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1483 = false ∨ valuation q 1492 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1493 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1493)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 2 3 (meaning1463 q) (meaning1484 q) (meaning1493 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1484 = false ∨ valuation q 1493 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1494 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1494)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 2 4 (meaning1463 q) (meaning1485 q) (meaning1494 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1485 = false ∨ valuation q 1494 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1492)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 3 1 (meaning1464 q) (meaning1482 q) (meaning1492 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1482 = false ∨ valuation q 1492 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1493)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 3 2 (meaning1464 q) (meaning1483 q) (meaning1493 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1483 = false ∨ valuation q 1493 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1494 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1494)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 3 3 (meaning1464 q) (meaning1484 q) (meaning1494 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1484 = false ∨ valuation q 1494 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true := by
  have hs : count1489 q = (countLit q [-81, -82, -85, -87, -89, -92, -93]) + (countLit q [-96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -87, -89, -92, -93]) (l₂ := [-96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1494)) (countLit q [-81, -82, -85, -87, -89, -92, -93]) (countLit q [-96, -97, -99, -102, -103, -105, -108]) (count1489 q) 4 2 (meaning1465 q) (meaning1483 q) (meaning1494 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1483 = false ∨ valuation q 1494 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1505 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1505)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 1 3 (meaning1436 q) (meaning1491 q) (meaning1505 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1491 = false ∨ valuation q 1505 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1506 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1506)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 1 4 (meaning1436 q) (meaning1492 q) (meaning1506 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1492 = false ∨ valuation q 1506 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1507 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1507)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 1 5 (meaning1436 q) (meaning1493 q) (meaning1507 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1493 = false ∨ valuation q 1507 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1506 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1506)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 2 3 (meaning1437 q) (meaning1491 q) (meaning1506 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1491 = false ∨ valuation q 1506 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1507 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1507)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 2 4 (meaning1437 q) (meaning1492 q) (meaning1507 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1492 = false ∨ valuation q 1507 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1508 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1508)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 2 5 (meaning1437 q) (meaning1493 q) (meaning1508 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1493 = false ∨ valuation q 1508 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1509 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1509)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 2 6 (meaning1437 q) (meaning1494 q) (meaning1509 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1494 = false ∨ valuation q 1509 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1507 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1507)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 3 3 (meaning1438 q) (meaning1491 q) (meaning1507 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1491 = false ∨ valuation q 1507 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1508 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1508)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 3 4 (meaning1438 q) (meaning1492 q) (meaning1508 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1492 = false ∨ valuation q 1508 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1509 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1509)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 3 5 (meaning1438 q) (meaning1493 q) (meaning1509 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1493 = false ∨ valuation q 1509 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1508 = true := by
  have hs : count1502 q = (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) + (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (l₂ := [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1508)) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]) (countLit q [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1502 q) 4 3 (meaning1439 q) (meaning1491 q) (meaning1508 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1491 = false ∨ valuation q 1508 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1527 = true := by
  have hs : count1515 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) + (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (l₂ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1515 q) 5 8 (meaning1391 q) (meaning1509 q) (meaning1527 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1509 = false ∨ valuation q 1527 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1527 = true := by
  have hs : count1515 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) + (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (l₂ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1515 q) 6 7 (meaning1392 q) (meaning1508 q) (meaning1527 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1508 = false ∨ valuation q 1527 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1527 = true := by
  have hs : count1515 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) + (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (l₂ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1515 q) 7 6 (meaning1393 q) (meaning1507 q) (meaning1527 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1507 = false ∨ valuation q 1527 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1527 = true := by
  have hs : count1515 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) + (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (l₂ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1515 q) 8 5 (meaning1394 q) (meaning1506 q) (meaning1527 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1506 = false ∨ valuation q 1527 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1527 = true := by
  have hs : count1515 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) + (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (l₂ := [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (countLit q [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]) (count1515 q) 9 4 (meaning1395 q) (meaning1505 q) (meaning1527 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1505 = false ∨ valuation q 1527 = true := counterClause415 (baseVal q)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false := by
  rw [value1527]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1515 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem block12 (q : Snake 81) (h : Conditions q) : B112E190.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112190
