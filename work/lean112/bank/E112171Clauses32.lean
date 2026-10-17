import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1613 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1613)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 6 5 (meaning1535 q) (meaning1592 q) (meaning1613 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1592 = false ∨ valuation q 1613 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1611 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1611)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 7 2 (meaning1536 q) (meaning1589 q) (meaning1611 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1589 = false ∨ valuation q 1611 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1612 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1612)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 7 3 (meaning1536 q) (meaning1590 q) (meaning1612 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1590 = false ∨ valuation q 1612 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1613 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1613)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 7 4 (meaning1536 q) (meaning1591 q) (meaning1613 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1591 = false ∨ valuation q 1613 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) + (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (l₂ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1620 q) 6 11 (meaning1478 q) (meaning1613 q) (meaning1636 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1613 = false ∨ valuation q 1636 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) + (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (l₂ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1620 q) 7 10 (meaning1479 q) (meaning1612 q) (meaning1636 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1612 = false ∨ valuation q 1636 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) + (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (l₂ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1620 q) 8 9 (meaning1480 q) (meaning1611 q) (meaning1636 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1611 = false ∨ valuation q 1636 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) + (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (l₂ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1620 q) 9 8 (meaning1481 q) (meaning1610 q) (meaning1636 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1610 = false ∨ valuation q 1636 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) + (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (l₂ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1620 q) 10 7 (meaning1482 q) (meaning1609 q) (meaning1636 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1609 = false ∨ valuation q 1636 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) + (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (l₂ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1620 q) 11 6 (meaning1483 q) (meaning1608 q) (meaning1636 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1608 = false ∨ valuation q 1636 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) + (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (l₂ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85, -86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1620 q) 12 5 (meaning1484 q) (meaning1607 q) (meaning1636 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1607 = false ∨ valuation q 1636 = true := counterClause1035 (baseVal q)

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false := by
  rw [value1636]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1620 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value4, value6, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (11 : Vertex) (15 : Vertex) (267 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value14, value15, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (134 : Vertex) (135 : Vertex) (390 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value16, value17, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (137 : Vertex) (200 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value44, value47, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (260 : Vertex) (264 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value44, value51, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (264 : Vertex) (320 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value44, value51, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (264 : Vertex) (384 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 57 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value45, value57, value66, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (273 : Vertex) (321 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value47, value48, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value50, value56, value60, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value50, value56, value68, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (327 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (267 : Vertex) (270 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value52, value53, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (267 : Vertex) (282 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 71 = false ∨ valuation q 73 = false := by
  rw [value53, value56, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (331 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value53, value56, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (395 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value65, value66, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value70, value71, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (331 : Vertex) (333 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value75, value77, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (338 : Vertex) (342 : Vertex) (346 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value82, value83, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (392 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value87, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (397 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E171.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h⟩

end
end Snake9.Regrowth.E112171
