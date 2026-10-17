import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1548)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 3 5 (meaning1512 q) (meaning1537 q) (meaning1548 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1537 = false ∨ valuation q 1548 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1513)) (literal (valuationOf q) (1544)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 4 (meaning1513 q) (meaning1544 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1544 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1545)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 4 1 (meaning1513 q) (meaning1533 q) (meaning1545 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1533 = false ∨ valuation q 1545 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1546)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 4 2 (meaning1513 q) (meaning1534 q) (meaning1546 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1534 = false ∨ valuation q 1546 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1547)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 4 3 (meaning1513 q) (meaning1535 q) (meaning1547 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1535 = false ∨ valuation q 1547 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1548)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 4 4 (meaning1513 q) (meaning1536 q) (meaning1548 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1536 = false ∨ valuation q 1548 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1546)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 5 1 (meaning1514 q) (meaning1533 q) (meaning1546 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1533 = false ∨ valuation q 1546 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1547)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 5 2 (meaning1514 q) (meaning1534 q) (meaning1547 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1534 = false ∨ valuation q 1547 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1548)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 5 3 (meaning1514 q) (meaning1535 q) (meaning1548 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1535 = false ∨ valuation q 1548 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1556)) (countLit q [-31]) (countLit q [-33]) (count1556 q) 1 (meaningNeg33 q) (meaning1556 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1556 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1556)) (countLit q [-31]) (countLit q [-33]) (count1556 q) 1 (meaningNeg31 q) (meaning1556 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1556 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1557 = true := by
  have hs : count1556 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1557)) (countLit q [-31]) (countLit q [-33]) (count1556 q) 1 1 (meaningNeg31 q) (meaningNeg33 q) (meaning1557 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 1557 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1558)) (countLit q [-34]) (countLit q [-36]) (count1558 q) 1 (meaningNeg36 q) (meaning1558 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1558 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1558)) (countLit q [-34]) (countLit q [-36]) (count1558 q) 1 (meaningNeg34 q) (meaning1558 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1558 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1559)) (countLit q [-34]) (countLit q [-36]) (count1558 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning1559 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 1559 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 1 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 2 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 1 1 (meaning1556 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1562)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 1 2 (meaning1556 q) (meaning1559 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1559 = false ∨ valuation q 1562 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 2 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 2 1 (meaning1557 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true := by
  have hs : count1560 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1563)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1560 q) 2 2 (meaning1557 q) (meaning1559 q) (meaning1563 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1559 = false ∨ valuation q 1563 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-37]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1564)) (countLit q [-37]) (countLit q [-41]) (count1564 q) 1 (meaningNeg41 q) (meaning1564 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1564 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-37]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1564)) (countLit q [-37]) (countLit q [-41]) (count1564 q) 1 (meaningNeg37 q) (meaning1564 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1564 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-37]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1565)) (countLit q [-37]) (countLit q [-41]) (count1564 q) 1 1 (meaningNeg37 q) (meaningNeg41 q) (meaning1565 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 41 = true ∨ valuation q 1565 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (1566)) (countLit q [-42]) (countLit q [-43]) (count1566 q) 1 (meaningNeg43 q) (meaning1566 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1566 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1566)) (countLit q [-42]) (countLit q [-43]) (count1566 q) 1 (meaningNeg42 q) (meaning1566 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1566 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 43 = true ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (1567)) (countLit q [-42]) (countLit q [-43]) (count1566 q) 1 1 (meaningNeg42 q) (meaningNeg43 q) (meaning1567 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 43 = true ∨ valuation q 1567 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-37, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -41]) (l₂ := [-42, -43])
  have hm := merge_right (literal (valuationOf q) (1566)) (literal (valuationOf q) (1568)) (countLit q [-37, -41]) (countLit q [-42, -43]) (count1568 q) 1 (meaning1566 q) (meaning1568 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1568 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-37, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -41]) (l₂ := [-42, -43])
  have hm := merge_right (literal (valuationOf q) (1567)) (literal (valuationOf q) (1569)) (countLit q [-37, -41]) (countLit q [-42, -43]) (count1568 q) 2 (meaning1567 q) (meaning1569 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1569 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-37, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -41]) (l₂ := [-42, -43])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-37, -41]) (countLit q [-42, -43]) (count1568 q) 1 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E186.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112186
