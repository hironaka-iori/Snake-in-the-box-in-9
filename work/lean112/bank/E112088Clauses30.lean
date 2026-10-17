import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 2 (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1531 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 3 (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1532 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1531)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 1 1 (meaning1519 q) (meaning1526 q) (meaning1531 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1526 = false ∨ valuation q 1531 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1532)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 1 2 (meaning1519 q) (meaning1527 q) (meaning1532 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1527 = false ∨ valuation q 1532 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1533)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 1 3 (meaning1519 q) (meaning1528 q) (meaning1533 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1528 = false ∨ valuation q 1533 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1533)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 2 2 (meaning1520 q) (meaning1527 q) (meaning1533 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1527 = false ∨ valuation q 1533 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1534 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1534)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 2 3 (meaning1520 q) (meaning1528 q) (meaning1534 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1528 = false ∨ valuation q 1534 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1537)) (countLit q [-73]) (countLit q [-75]) (count1537 q) 1 (meaningNeg75 q) (meaning1537 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1537 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1537)) (countLit q [-73]) (countLit q [-75]) (count1537 q) 1 (meaningNeg73 q) (meaning1537 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1537 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 75 = true ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (1538)) (countLit q [-73]) (countLit q [-75]) (count1537 q) 1 1 (meaningNeg73 q) (meaningNeg75 q) (meaning1538 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 75 = true ∨ valuation q 1538 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1539)) (countLit q [-77]) (countLit q [-78]) (count1539 q) 1 (meaningNeg78 q) (meaning1539 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1539 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-73, -75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1539)) (literal (valuationOf q) (1541)) (countLit q [-73, -75]) (countLit q [-77, -78]) (count1541 q) 1 (meaning1539 q) (meaning1541 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1541 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-73, -75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1537)) (literal (valuationOf q) (1541)) (countLit q [-73, -75]) (countLit q [-77, -78]) (count1541 q) 1 (meaning1537 q) (meaning1541 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1541 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-73, -75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-73, -75]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-73, -75]) (countLit q [-77, -78]) (count1541 q) 2 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1545)) (countLit q [-80]) (countLit q [-82]) (count1545 q) 1 (meaningNeg82 q) (meaning1545 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1545 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1547)) (countLit q [-85]) (countLit q [-87]) (count1547 q) 1 (meaningNeg87 q) (meaning1547 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1547 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1547)) (countLit q [-85]) (countLit q [-87]) (count1547 q) 1 (meaningNeg85 q) (meaning1547 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1547 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1548)) (countLit q [-85]) (countLit q [-87]) (count1547 q) 1 1 (meaningNeg85 q) (meaningNeg87 q) (meaning1548 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 1548 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-80, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-85, -87])
  have hm := merge_right (literal (valuationOf q) (1547)) (literal (valuationOf q) (1549)) (countLit q [-80, -82]) (countLit q [-85, -87]) (count1549 q) 1 (meaning1547 q) (meaning1549 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1549 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-80, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-85, -87])
  have hm := merge_right (literal (valuationOf q) (1548)) (literal (valuationOf q) (1550)) (countLit q [-80, -82]) (countLit q [-85, -87]) (count1549 q) 2 (meaning1548 q) (meaning1550 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1550 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-80, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-85, -87])
  have hm := merge_left (literal (valuationOf q) (1545)) (literal (valuationOf q) (1549)) (countLit q [-80, -82]) (countLit q [-85, -87]) (count1549 q) 1 (meaning1545 q) (meaning1549 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1549 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-80, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-85, -87])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1550)) (countLit q [-80, -82]) (countLit q [-85, -87]) (count1549 q) 1 1 (meaning1545 q) (meaning1547 q) (meaning1550 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1547 = false ∨ valuation q 1550 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-80, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-85, -87])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1551)) (countLit q [-80, -82]) (countLit q [-85, -87]) (count1549 q) 1 2 (meaning1545 q) (meaning1548 q) (meaning1551 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1548 = false ∨ valuation q 1551 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_right (literal (valuationOf q) (1549)) (literal (valuationOf q) (1553)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 1 (meaning1549 q) (meaning1553 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1553 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_right (literal (valuationOf q) (1550)) (literal (valuationOf q) (1554)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 2 (meaning1550 q) (meaning1554 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1554 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1555)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 3 (meaning1551 q) (meaning1555 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1555 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (1541)) (literal (valuationOf q) (1553)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 1 (meaning1541 q) (meaning1553 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1553 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1554)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 1 1 (meaning1541 q) (meaning1549 q) (meaning1554 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1549 = false ∨ valuation q 1554 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1555)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 1 2 (meaning1541 q) (meaning1550 q) (meaning1555 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1550 = false ∨ valuation q 1555 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1556)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 1 3 (meaning1541 q) (meaning1551 q) (meaning1556 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1551 = false ∨ valuation q 1556 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-73, -75, -77, -78]) + (countLit q [-80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-73, -75, -77, -78]) (l₂ := [-80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1557)) (countLit q [-73, -75, -77, -78]) (countLit q [-80, -82, -85, -87]) (count1553 q) 2 3 (meaning1542 q) (meaning1551 q) (meaning1557 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1551 = false ∨ valuation q 1557 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1562 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1562)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 1 1 (meaning1530 q) (meaning1553 q) (meaning1562 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1553 = false ∨ valuation q 1562 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E088.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112088
