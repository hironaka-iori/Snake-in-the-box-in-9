import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1543 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1543)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 7 6 (meaning1463 q) (meaning1521 q) (meaning1543 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1521 = false ∨ valuation q 1543 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 8 2 (meaning1464 q) (meaning1517 q) (meaning1540 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1517 = false ∨ valuation q 1540 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 8 3 (meaning1464 q) (meaning1518 q) (meaning1541 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1518 = false ∨ valuation q 1541 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1542)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 8 4 (meaning1464 q) (meaning1519 q) (meaning1542 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1519 = false ∨ valuation q 1542 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1543 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1543)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 8 5 (meaning1464 q) (meaning1520 q) (meaning1543 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1520 = false ∨ valuation q 1543 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1543 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1543)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 9 4 (meaning1465 q) (meaning1519 q) (meaning1543 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1519 = false ∨ valuation q 1543 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-60]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1551)) (countLit q [-60]) (countLit q [-63]) (count1551 q) 1 (meaningNeg63 q) (meaning1551 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1551 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-59]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -63])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (countLit q [-59]) (countLit q [-60, -63]) (count1553 q) 1 (meaning1551 q) (meaning1553 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1556)) (countLit q [-65]) (countLit q [-67]) (count1556 q) 1 (meaningNeg67 q) (meaning1556 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1556 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1556)) (countLit q [-65]) (countLit q [-67]) (count1556 q) 1 (meaningNeg65 q) (meaning1556 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1556 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1557 = true := by
  have hs : count1556 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1557)) (countLit q [-65]) (countLit q [-67]) (count1556 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning1557 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 1557 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1558)) (countLit q [-69]) (countLit q [-72]) (count1558 q) 1 (meaningNeg72 q) (meaning1558 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1558 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1558)) (countLit q [-69]) (countLit q [-72]) (count1558 q) 1 (meaningNeg69 q) (meaning1558 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1558 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1559)) (countLit q [-69]) (countLit q [-72]) (count1558 q) 1 1 (meaningNeg69 q) (meaningNeg72 q) (meaning1559 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 1559 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1560 q) 1 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1560 q) 2 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1560 q) 1 1 (meaning1556 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1562)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1560 q) 1 2 (meaning1556 q) (meaning1559 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1559 = false ∨ valuation q 1562 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1560 q) 2 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1560 q) 2 1 (meaning1557 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-59, -60, -63]) + (countLit q [-65, -67, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63]) (l₂ := [-65, -67, -69, -72])
  have hm := merge_right (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-59, -60, -63]) (countLit q [-65, -67, -69, -72]) (count1564 q) 1 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-59, -60, -63]) + (countLit q [-65, -67, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63]) (l₂ := [-65, -67, -69, -72])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-59, -60, -63]) (countLit q [-65, -67, -69, -72]) (count1564 q) 2 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-59, -60, -63]) + (countLit q [-65, -67, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63]) (l₂ := [-65, -67, -69, -72])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-59, -60, -63]) (countLit q [-65, -67, -69, -72]) (count1564 q) 3 (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1566 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-59, -60, -63]) + (countLit q [-65, -67, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63]) (l₂ := [-65, -67, -69, -72])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1564)) (countLit q [-59, -60, -63]) (countLit q [-65, -67, -69, -72]) (count1564 q) 1 (meaning1553 q) (meaning1564 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1564 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-59, -60, -63]) + (countLit q [-65, -67, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63]) (l₂ := [-65, -67, -69, -72])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1565)) (countLit q [-59, -60, -63]) (countLit q [-65, -67, -69, -72]) (count1564 q) 1 1 (meaning1553 q) (meaning1560 q) (meaning1565 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1560 = false ∨ valuation q 1565 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-59, -60, -63]) + (countLit q [-65, -67, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63]) (l₂ := [-65, -67, -69, -72])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1566)) (countLit q [-59, -60, -63]) (countLit q [-65, -67, -69, -72]) (count1564 q) 1 2 (meaning1553 q) (meaning1561 q) (meaning1566 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1561 = false ∨ valuation q 1566 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-73]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1571)) (countLit q [-73]) (countLit q [-76]) (count1571 q) 1 (meaningNeg76 q) (meaning1571 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1571 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-73]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1571)) (countLit q [-73]) (countLit q [-76]) (count1571 q) 1 (meaningNeg73 q) (meaning1571 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1571 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-73]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1572)) (countLit q [-73]) (countLit q [-76]) (count1571 q) 1 1 (meaningNeg73 q) (meaningNeg76 q) (meaning1572 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 76 = true ∨ valuation q 1572 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1573)) (countLit q [-77]) (countLit q [-80]) (count1573 q) 1 (meaningNeg80 q) (meaning1573 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1573 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1573)) (countLit q [-77]) (countLit q [-80]) (count1573 q) 1 (meaningNeg77 q) (meaning1573 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1573 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E104.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112104
