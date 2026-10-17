import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-82, -85, -86, -88, -93, -94, -97]) + (countLit q [-99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86, -88, -93, -94, -97]) (l₂ := [-99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1540)) (countLit q [-82, -85, -86, -88, -93, -94, -97]) (countLit q [-99, -100, -103, -105, -106, -108, -109]) (count1539 q) 1 1 (meaning1512 q) (meaning1532 q) (meaning1540 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1532 = false ∨ valuation q 1540 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-82, -85, -86, -88, -93, -94, -97]) + (countLit q [-99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86, -88, -93, -94, -97]) (l₂ := [-99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1541)) (countLit q [-82, -85, -86, -88, -93, -94, -97]) (countLit q [-99, -100, -103, -105, -106, -108, -109]) (count1539 q) 2 1 (meaning1513 q) (meaning1532 q) (meaning1541 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1532 = false ∨ valuation q 1541 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-82, -85, -86, -88, -93, -94, -97]) + (countLit q [-99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86, -88, -93, -94, -97]) (l₂ := [-99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1542)) (countLit q [-82, -85, -86, -88, -93, -94, -97]) (countLit q [-99, -100, -103, -105, -106, -108, -109]) (count1539 q) 3 1 (meaning1514 q) (meaning1532 q) (meaning1542 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1532 = false ∨ valuation q 1542 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-82, -85, -86, -88, -93, -94, -97]) + (countLit q [-99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86, -88, -93, -94, -97]) (l₂ := [-99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1543)) (countLit q [-82, -85, -86, -88, -93, -94, -97]) (countLit q [-99, -100, -103, -105, -106, -108, -109]) (count1539 q) 4 1 (meaning1515 q) (meaning1532 q) (meaning1543 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1532 = false ∨ valuation q 1543 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1557)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 2 3 (meaning1486 q) (meaning1541 q) (meaning1557 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1541 = false ∨ valuation q 1557 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1558)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 2 4 (meaning1486 q) (meaning1542 q) (meaning1558 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1542 = false ∨ valuation q 1558 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1559)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 2 5 (meaning1486 q) (meaning1543 q) (meaning1559 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1543 = false ∨ valuation q 1559 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1557)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 3 2 (meaning1487 q) (meaning1540 q) (meaning1557 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1540 = false ∨ valuation q 1557 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1558)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 3 3 (meaning1487 q) (meaning1541 q) (meaning1558 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1541 = false ∨ valuation q 1558 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1559)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 3 4 (meaning1487 q) (meaning1542 q) (meaning1559 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1542 = false ∨ valuation q 1559 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1558)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 4 2 (meaning1488 q) (meaning1540 q) (meaning1558 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1540 = false ∨ valuation q 1558 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) + (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (l₂ := [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]) (countLit q [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1553 q) 4 3 (meaning1488 q) (meaning1541 q) (meaning1559 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1541 = false ∨ valuation q 1559 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1582 = true := by
  have hs : count1568 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) + (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (l₂ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1582)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1568 q) 8 7 (meaning1437 q) (meaning1559 q) (meaning1582 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1559 = false ∨ valuation q 1582 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1582 = true := by
  have hs : count1568 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) + (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (l₂ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1582)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1568 q) 9 6 (meaning1438 q) (meaning1558 q) (meaning1582 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1558 = false ∨ valuation q 1582 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1582 = true := by
  have hs : count1568 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) + (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (l₂ := [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1582)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (countLit q [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]) (count1568 q) 10 5 (meaning1439 q) (meaning1557 q) (meaning1582 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1557 = false ∨ valuation q 1582 = true := counterClause527 (baseVal q)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false := by
  rw [value1582]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1568 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 18 = false := by
  rw [value1, value3, value8, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (11 : Vertex) (27 : Vertex) (75 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value4, value6, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (67 : Vertex) (81 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 45 = false ∨ valuation q 54 = false := by
  rw [value8, value18, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (91 : Vertex) (203 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 69 = false ∨ valuation q 79 = false := by
  rw [value8, value18, value69, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (91 : Vertex) (331 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value11, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (81 : Vertex) (82 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value13, value17, value72, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (82 : Vertex) (90 : Vertex) (338 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value35, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (156 : Vertex) (157 : Vertex) (158 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value41, value42, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value44, value45, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (201 : Vertex) (203 : Vertex) (217 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value65, value66, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (326 : Vertex) (327 : Vertex) (342 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value68, value69, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (331 : Vertex) (345 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E148.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h⟩

end
end Snake9.Regrowth.E112148
