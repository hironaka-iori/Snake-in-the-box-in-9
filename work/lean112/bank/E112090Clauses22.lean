import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1506)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 2 2 (meaning1477 q) (meaning1497 q) (meaning1506 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1497 = false ∨ valuation q 1506 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1505)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 3 (meaning1478 q) (meaning1505 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1505 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1506)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 3 1 (meaning1478 q) (meaning1496 q) (meaning1506 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1496 = false ∨ valuation q 1506 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1507)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 3 2 (meaning1478 q) (meaning1497 q) (meaning1507 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1497 = false ∨ valuation q 1507 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1479)) (literal (valuationOf q) (1506)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 4 (meaning1479 q) (meaning1506 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1506 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1507)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 4 1 (meaning1479 q) (meaning1496 q) (meaning1507 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1496 = false ∨ valuation q 1507 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1508 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1508)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 5 1 (meaning1480 q) (meaning1496 q) (meaning1508 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1496 = false ∨ valuation q 1508 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1508 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1508)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 6 (meaning1481 q) (meaning1508 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1508 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1522 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1522)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 2 4 (meaning1450 q) (meaning1506 q) (meaning1522 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1506 = false ∨ valuation q 1522 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1523)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 2 5 (meaning1450 q) (meaning1507 q) (meaning1523 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1507 = false ∨ valuation q 1523 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1524)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 2 6 (meaning1450 q) (meaning1508 q) (meaning1524 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1508 = false ∨ valuation q 1524 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1521 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1521)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 3 2 (meaning1451 q) (meaning1504 q) (meaning1521 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1504 = false ∨ valuation q 1521 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1522 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1522)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 3 3 (meaning1451 q) (meaning1505 q) (meaning1522 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1505 = false ∨ valuation q 1522 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1523)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 3 4 (meaning1451 q) (meaning1506 q) (meaning1523 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1506 = false ∨ valuation q 1523 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1524)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 3 5 (meaning1451 q) (meaning1507 q) (meaning1524 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1507 = false ∨ valuation q 1524 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1521 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1521)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 4 1 (meaning1452 q) (meaning1503 q) (meaning1521 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1503 = false ∨ valuation q 1521 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1522 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1522)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 4 2 (meaning1452 q) (meaning1504 q) (meaning1522 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1504 = false ∨ valuation q 1522 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1523)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 4 3 (meaning1452 q) (meaning1505 q) (meaning1523 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1505 = false ∨ valuation q 1523 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1524)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 4 4 (meaning1452 q) (meaning1506 q) (meaning1524 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1506 = false ∨ valuation q 1524 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1525)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 4 5 (meaning1452 q) (meaning1507 q) (meaning1525 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1507 = false ∨ valuation q 1525 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1522 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1522)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 5 1 (meaning1453 q) (meaning1503 q) (meaning1522 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1503 = false ∨ valuation q 1522 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1523)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 5 2 (meaning1453 q) (meaning1504 q) (meaning1523 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1504 = false ∨ valuation q 1523 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1524)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 5 3 (meaning1453 q) (meaning1505 q) (meaning1524 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1505 = false ∨ valuation q 1524 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1525)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 5 4 (meaning1453 q) (meaning1506 q) (meaning1525 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1506 = false ∨ valuation q 1525 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1523)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 6 1 (meaning1454 q) (meaning1503 q) (meaning1523 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1503 = false ∨ valuation q 1523 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1524)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 6 2 (meaning1454 q) (meaning1504 q) (meaning1524 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1504 = false ∨ valuation q 1524 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1525)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 6 3 (meaning1454 q) (meaning1505 q) (meaning1525 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1505 = false ∨ valuation q 1525 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1526 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1526)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 6 4 (meaning1454 q) (meaning1506 q) (meaning1526 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1506 = false ∨ valuation q 1526 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1524)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 7 1 (meaning1455 q) (meaning1503 q) (meaning1524 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1503 = false ∨ valuation q 1524 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) + (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (l₂ := [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1525)) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]) (countLit q [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1517 q) 7 2 (meaning1455 q) (meaning1504 q) (meaning1525 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1504 = false ∨ valuation q 1525 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) + (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (l₂ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1532 q) 5 10 (meaning1398 q) (meaning1526 q) (meaning1546 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1526 = false ∨ valuation q 1546 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) + (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (l₂ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1532 q) 6 9 (meaning1399 q) (meaning1525 q) (meaning1546 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1525 = false ∨ valuation q 1546 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E090.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112090
