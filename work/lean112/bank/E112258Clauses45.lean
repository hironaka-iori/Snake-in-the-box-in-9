import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 3 15 (meaning1616 q) (meaning1759 q) (meaning1780 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1759 = false ∨ valuation q 1780 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 4 14 (meaning1617 q) (meaning1758 q) (meaning1780 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1758 = false ∨ valuation q 1780 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 5 13 (meaning1618 q) (meaning1757 q) (meaning1780 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1757 = false ∨ valuation q 1780 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 6 12 (meaning1619 q) (meaning1756 q) (meaning1780 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1756 = false ∨ valuation q 1780 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 7 11 (meaning1620 q) (meaning1755 q) (meaning1780 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1755 = false ∨ valuation q 1780 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 8 10 (meaning1621 q) (meaning1754 q) (meaning1780 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1754 = false ∨ valuation q 1780 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 9 9 (meaning1622 q) (meaning1753 q) (meaning1780 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1753 = false ∨ valuation q 1780 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 10 8 (meaning1623 q) (meaning1752 q) (meaning1780 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1752 = false ∨ valuation q 1780 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 11 7 (meaning1624 q) (meaning1751 q) (meaning1780 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1751 = false ∨ valuation q 1780 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 12 6 (meaning1625 q) (meaning1750 q) (meaning1780 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1750 = false ∨ valuation q 1780 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) + (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (l₂ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31, -33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88, -90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1763 q) 13 5 (meaning1626 q) (meaning1749 q) (meaning1780 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1749 = false ∨ valuation q 1780 = true := counterClause1451 (baseVal q)

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false := by
  rw [value1780]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1763 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 15 = false ∨ valuation q 65 = false ∨ valuation q 74 = false := by
  rw [value6, value15, value65, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (273 : Vertex) (385 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 25 = false ∨ valuation q 66 = false ∨ valuation q 83 = false := by
  rw [value7, value25, value66, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (290 : Vertex) (386 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value8, value9, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (263 : Vertex) (293 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value8, value9, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (263 : Vertex) (389 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 26 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value8, value26, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (293 : Vertex) (389 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 23 = false := by
  rw [value9, value13, value18, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value9, value13, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (391 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value9, value18, value69, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (279 : Vertex) (391 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 29 = false ∨ valuation q 32 = false := by
  rw [value10, value12, value29, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (268 : Vertex) (296 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 32 = false ∨ valuation q 71 = false ∨ valuation q 90 = false := by
  rw [value12, value32, value71, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (300 : Vertex) (396 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value14, value17, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (272 : Vertex) (276 : Vertex) (400 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value15, value16, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (305 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value15, value19, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (281 : Vertex) (401 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value20, value22, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (282 : Vertex) (286 : Vertex) (410 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value21, value23, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (285 : Vertex) (287 : Vertex) (317 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value22, value23, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (286 : Vertex) (287 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 41 = false ∨ valuation q 81 = false ∨ valuation q 101 = false := by
  rw [value23, value41, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (287 : Vertex) (319 : Vertex) (415 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 51 = false ∨ valuation q 81 = false ∨ valuation q 109 = false := by
  rw [value23, value51, value81, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (287 : Vertex) (351 : Vertex) (415 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value24, value25, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (290 : Vertex) (352 : Vertex) (354 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value24, value25, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (290 : Vertex) (416 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E258.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112258
