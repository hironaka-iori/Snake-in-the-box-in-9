import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1006 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 8 4 (meaning922 q) (meaning982 q) (meaning1006 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 982 = false ∨ valuation q 1006 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1007 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1007)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 8 5 (meaning922 q) (meaning983 q) (meaning1007 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 983 = false ∨ valuation q 1007 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1006 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 9 3 (meaning923 q) (meaning981 q) (meaning1006 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 981 = false ∨ valuation q 1006 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1007 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1007)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 9 4 (meaning923 q) (meaning982 q) (meaning1007 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 982 = false ∨ valuation q 1007 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1019 = true := by
  have hs : count1019 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1019)) (countLit q [-65]) (countLit q [-67]) (count1019 q) 1 (meaningNeg67 q) (meaning1019 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1019 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1020 = true := by
  have hs : count1019 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1020)) (countLit q [-65]) (countLit q [-67]) (count1019 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning1020 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 1020 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1021 = true := by
  have hs : count1021 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1021)) (countLit q [-69]) (countLit q [-72]) (count1021 q) 1 (meaningNeg72 q) (meaning1021 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1021 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1021 = true := by
  have hs : count1021 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1021)) (countLit q [-69]) (countLit q [-72]) (count1021 q) 1 (meaningNeg69 q) (meaning1021 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1021 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1022 = true := by
  have hs : count1021 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1022)) (countLit q [-69]) (countLit q [-72]) (count1021 q) 1 1 (meaningNeg69 q) (meaningNeg72 q) (meaning1022 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 1022 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1025 = true := by
  have hs : count1023 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1025)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1023 q) 1 2 (meaning1019 q) (meaning1022 q) (meaning1025 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1022 = false ∨ valuation q 1025 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1024 = true := by
  have hs : count1023 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_left (literal (valuationOf q) (1020)) (literal (valuationOf q) (1024)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1023 q) 2 (meaning1020 q) (meaning1024 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1024 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1025 = true := by
  have hs : count1023 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1025)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1023 q) 2 1 (meaning1020 q) (meaning1021 q) (meaning1025 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1021 = false ∨ valuation q 1025 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1026 = true := by
  have hs : count1023 q = (countLit q [-65, -67]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -72])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1026)) (countLit q [-65, -67]) (countLit q [-69, -72]) (count1023 q) 2 2 (meaning1020 q) (meaning1022 q) (meaning1026 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1022 = false ∨ valuation q 1026 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1027 = true := by
  have hs : count1027 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1027)) (countLit q [-73]) (countLit q [-75]) (count1027 q) 1 (meaningNeg75 q) (meaning1027 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1027 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1027 = true := by
  have hs : count1027 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1027)) (countLit q [-73]) (countLit q [-75]) (count1027 q) 1 (meaningNeg73 q) (meaning1027 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1027 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 75 = true ∨ valuationOf q 1028 = true := by
  have hs : count1027 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (1028)) (countLit q [-73]) (countLit q [-75]) (count1027 q) 1 1 (meaningNeg73 q) (meaningNeg75 q) (meaning1028 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 75 = true ∨ valuation q 1028 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1029 = true := by
  have hs : count1029 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1029)) (countLit q [-77]) (countLit q [-79]) (count1029 q) 1 (meaningNeg79 q) (meaning1029 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1029 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1029 = true := by
  have hs : count1029 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1029)) (countLit q [-77]) (countLit q [-79]) (count1029 q) 1 (meaningNeg77 q) (meaning1029 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1029 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1030 = true := by
  have hs : count1029 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1030)) (countLit q [-77]) (countLit q [-79]) (count1029 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1030 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1030 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 1029 = false ∨ valuationOf q 1031 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1029)) (literal (valuationOf q) (1031)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 1 (meaning1029 q) (meaning1031 q) hs
  change valuationOf q 1029 = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 1029 = false ∨ valuation q 1031 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1030 = false ∨ valuationOf q 1032 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1030)) (literal (valuationOf q) (1032)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 2 (meaning1030 q) (meaning1032 q) hs
  change valuationOf q 1030 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1030 = false ∨ valuation q 1032 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1031 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_left (literal (valuationOf q) (1027)) (literal (valuationOf q) (1031)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 1 (meaning1027 q) (meaning1031 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1031 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1032 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1027)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1032)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 1 1 (meaning1027 q) (meaning1029 q) (meaning1032 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1029 = false ∨ valuation q 1032 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1033 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1027)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1033)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 1 2 (meaning1027 q) (meaning1030 q) (meaning1033 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1030 = false ∨ valuation q 1033 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1032 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_left (literal (valuationOf q) (1028)) (literal (valuationOf q) (1032)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 2 (meaning1028 q) (meaning1032 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1032 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1033 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1028)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1033)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 2 1 (meaning1028 q) (meaning1029 q) (meaning1033 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1029 = false ∨ valuation q 1033 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1034 = true := by
  have hs : count1031 q = (countLit q [-73, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1028)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1034)) (countLit q [-73, -75]) (countLit q [-77, -79]) (count1031 q) 2 2 (meaning1028 q) (meaning1030 q) (meaning1034 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1030 = false ∨ valuation q 1034 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1036 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_left (literal (valuationOf q) (1024)) (literal (valuationOf q) (1036)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 2 (meaning1024 q) (meaning1036 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1036 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1037 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1031)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 2 1 (meaning1024 q) (meaning1031 q) (meaning1037 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1031 = false ∨ valuation q 1037 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1038 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 2 2 (meaning1024 q) (meaning1032 q) (meaning1038 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1032 = false ∨ valuation q 1038 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1039 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 2 3 (meaning1024 q) (meaning1033 q) (meaning1039 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1033 = false ∨ valuation q 1039 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1040 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 2 4 (meaning1024 q) (meaning1034 q) (meaning1040 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1034 = false ∨ valuation q 1040 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E057.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112057
