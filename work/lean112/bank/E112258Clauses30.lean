import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1521 = false ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1524)) (countLit q [-18]) (countLit q [-21, -22]) (count1523 q) 1 1 (meaningNeg18 q) (meaning1521 q) (meaning1524 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1521 = false ∨ valuation q 1524 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1522 = false ∨ valuationOf q 1525 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1525)) (countLit q [-18]) (countLit q [-21, -22]) (count1523 q) 1 2 (meaningNeg18 q) (meaning1522 q) (meaning1525 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1522 = false ∨ valuation q 1525 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-25]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1526)) (countLit q [-25]) (countLit q [-28]) (count1526 q) 1 (meaningNeg28 q) (meaning1526 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1526 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-25]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1526)) (countLit q [-25]) (countLit q [-28]) (count1526 q) 1 (meaningNeg25 q) (meaning1526 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1526 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 28 = true ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-25]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (1527)) (countLit q [-25]) (countLit q [-28]) (count1526 q) 1 1 (meaningNeg25 q) (meaningNeg28 q) (meaning1527 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 28 = true ∨ valuation q 1527 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1528)) (countLit q [-29]) (countLit q [-31]) (count1528 q) 1 (meaningNeg31 q) (meaning1528 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1528 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1528)) (countLit q [-29]) (countLit q [-31]) (count1528 q) 1 (meaningNeg29 q) (meaning1528 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1528 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1529)) (countLit q [-29]) (countLit q [-31]) (count1528 q) 1 1 (meaningNeg29 q) (meaningNeg31 q) (meaning1529 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 1529 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 1 (meaning1528 q) (meaning1530 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 2 (meaning1529 q) (meaning1531 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 1 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 1 1 (meaning1526 q) (meaning1528 q) (meaning1531 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = false ∨ valuation q 1531 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1532)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 1 2 (meaning1526 q) (meaning1529 q) (meaning1532 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1529 = false ∨ valuation q 1532 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 2 (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1531 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 2 1 (meaning1527 q) (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1528 = false ∨ valuation q 1532 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-25, -28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -28]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-25, -28]) (countLit q [-29, -31]) (count1530 q) 2 2 (meaning1527 q) (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = false ∨ valuation q 1533 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 1 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 2 (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1535 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 3 (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1536 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 4 (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1523)) (literal (valuationOf q) (1534)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 1 (meaning1523 q) (meaning1534 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1534 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1535 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1535)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 1 1 (meaning1523 q) (meaning1530 q) (meaning1535 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1530 = false ∨ valuation q 1535 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1536 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1536)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 1 2 (meaning1523 q) (meaning1531 q) (meaning1536 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1531 = false ∨ valuation q 1536 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1537 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1537)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 1 3 (meaning1523 q) (meaning1532 q) (meaning1537 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1532 = false ∨ valuation q 1537 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1538)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 1 4 (meaning1523 q) (meaning1533 q) (meaning1538 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1533 = false ∨ valuation q 1538 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1535 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1524)) (literal (valuationOf q) (1535)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 2 (meaning1524 q) (meaning1535 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1535 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1536 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1536)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 2 1 (meaning1524 q) (meaning1530 q) (meaning1536 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1530 = false ∨ valuation q 1536 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1537 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1537)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 2 2 (meaning1524 q) (meaning1531 q) (meaning1537 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1531 = false ∨ valuation q 1537 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1538 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1538)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 2 3 (meaning1524 q) (meaning1532 q) (meaning1538 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1532 = false ∨ valuation q 1538 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1536 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1536)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 3 (meaning1525 q) (meaning1536 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1536 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1537 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1537)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 3 1 (meaning1525 q) (meaning1530 q) (meaning1537 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1530 = false ∨ valuation q 1537 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1538 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1538)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 3 2 (meaning1525 q) (meaning1531 q) (meaning1538 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1531 = false ∨ valuation q 1538 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E258.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112258
