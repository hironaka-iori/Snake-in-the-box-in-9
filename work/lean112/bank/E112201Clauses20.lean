import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1509)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 1 2 (meaning1481 q) (meaning1501 q) (meaning1509 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1501 = false ∨ valuation q 1509 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1510 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 1 3 (meaning1481 q) (meaning1502 q) (meaning1510 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1502 = false ∨ valuation q 1510 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1482)) (literal (valuationOf q) (1508)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 2 (meaning1482 q) (meaning1508 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1508 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1509)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 2 1 (meaning1482 q) (meaning1500 q) (meaning1509 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1500 = false ∨ valuation q 1509 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1510 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 2 2 (meaning1482 q) (meaning1501 q) (meaning1510 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1501 = false ∨ valuation q 1510 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1511 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 2 3 (meaning1482 q) (meaning1502 q) (meaning1511 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1502 = false ∨ valuation q 1511 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1510 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 3 1 (meaning1483 q) (meaning1500 q) (meaning1510 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1500 = false ∨ valuation q 1510 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1511 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 3 2 (meaning1483 q) (meaning1501 q) (meaning1511 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1501 = false ∨ valuation q 1511 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1511 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 4 1 (meaning1484 q) (meaning1500 q) (meaning1511 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1500 = false ∨ valuation q 1511 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1521)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 2 1 (meaning1460 q) (meaning1507 q) (meaning1521 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1507 = false ∨ valuation q 1521 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1522 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1522)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 2 2 (meaning1460 q) (meaning1508 q) (meaning1522 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1508 = false ∨ valuation q 1522 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1523)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 2 3 (meaning1460 q) (meaning1509 q) (meaning1523 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1509 = false ∨ valuation q 1523 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1524)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 2 4 (meaning1460 q) (meaning1510 q) (meaning1524 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1510 = false ∨ valuation q 1524 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1525)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 2 5 (meaning1460 q) (meaning1511 q) (meaning1525 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1511 = false ∨ valuation q 1525 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1522 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1522)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 3 1 (meaning1461 q) (meaning1507 q) (meaning1522 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1507 = false ∨ valuation q 1522 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1523)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 3 2 (meaning1461 q) (meaning1508 q) (meaning1523 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1508 = false ∨ valuation q 1523 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1524)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 3 3 (meaning1461 q) (meaning1509 q) (meaning1524 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1509 = false ∨ valuation q 1524 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1525)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 3 4 (meaning1461 q) (meaning1510 q) (meaning1525 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1510 = false ∨ valuation q 1525 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1524)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 4 2 (meaning1462 q) (meaning1508 q) (meaning1524 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1508 = false ∨ valuation q 1524 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1526)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1519 q) 4 4 (meaning1462 q) (meaning1510 q) (meaning1526 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1510 = false ∨ valuation q 1526 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1531 q) 4 8 (meaning1414 q) (meaning1526 q) (meaning1542 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1526 = false ∨ valuation q 1542 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1531 q) 5 7 (meaning1415 q) (meaning1525 q) (meaning1542 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1525 = false ∨ valuation q 1542 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1531 q) 6 6 (meaning1416 q) (meaning1524 q) (meaning1542 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1524 = false ∨ valuation q 1542 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1531 q) 7 5 (meaning1417 q) (meaning1523 q) (meaning1542 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1523 = false ∨ valuation q 1542 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1531 q) 8 4 (meaning1418 q) (meaning1522 q) (meaning1542 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1522 = false ∨ valuation q 1542 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]) (count1531 q) 9 3 (meaning1419 q) (meaning1521 q) (meaning1542 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1521 = false ∨ valuation q 1542 = true := counterClause666 (baseVal q)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false := by
  rw [value1542]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1531 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value13, value14, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value20, value21, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (173 : Vertex) (175 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value28, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value88, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E201.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h⟩

end
end Snake9.Regrowth.E112201
