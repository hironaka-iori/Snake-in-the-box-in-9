import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1532)) (countLit q [-56]) (countLit q [-57]) (count1531 q) 1 1 (meaningNeg56 q) (meaningNeg57 q) (meaning1532 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 1532 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 1 (meaning1531 q) (meaning1533 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1532)) (literal (valuationOf q) (1534)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 2 (meaning1532 q) (meaning1534 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1534 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 1 (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 1 1 (meaning1529 q) (meaning1531 q) (meaning1534 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1535)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 1 2 (meaning1529 q) (meaning1532 q) (meaning1535 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1532 = false ∨ valuation q 1535 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 2 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 2 1 (meaning1530 q) (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1531 = false ∨ valuation q 1535 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1533 q = (countLit q [-53, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-53, -55]) (countLit q [-56, -57]) (count1533 q) 2 2 (meaning1530 q) (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1532 = false ∨ valuation q 1536 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 1 (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 2 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 3 (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1539 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1540)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 4 (meaning1536 q) (meaning1540 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1540 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1537)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 1 (meaning1525 q) (meaning1537 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1537 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1538)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 1 1 (meaning1525 q) (meaning1533 q) (meaning1538 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1533 = false ∨ valuation q 1538 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1539)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 1 2 (meaning1525 q) (meaning1534 q) (meaning1539 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1534 = false ∨ valuation q 1539 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1540)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 1 3 (meaning1525 q) (meaning1535 q) (meaning1540 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1541)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 1 4 (meaning1525 q) (meaning1536 q) (meaning1541 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1536 = false ∨ valuation q 1541 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1538)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 2 (meaning1526 q) (meaning1538 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1538 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1539)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 2 1 (meaning1526 q) (meaning1533 q) (meaning1539 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1533 = false ∨ valuation q 1539 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1540)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 2 2 (meaning1526 q) (meaning1534 q) (meaning1540 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1534 = false ∨ valuation q 1540 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1541)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 2 3 (meaning1526 q) (meaning1535 q) (meaning1541 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1535 = false ∨ valuation q 1541 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1542)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 2 4 (meaning1526 q) (meaning1536 q) (meaning1542 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1536 = false ∨ valuation q 1542 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1527)) (literal (valuationOf q) (1539)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 3 (meaning1527 q) (meaning1539 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1539 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1540)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 3 1 (meaning1527 q) (meaning1533 q) (meaning1540 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1533 = false ∨ valuation q 1540 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1541)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 3 2 (meaning1527 q) (meaning1534 q) (meaning1541 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1534 = false ∨ valuation q 1541 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1542)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 3 3 (meaning1527 q) (meaning1535 q) (meaning1542 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1535 = false ∨ valuation q 1542 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1543)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 3 4 (meaning1527 q) (meaning1536 q) (meaning1543 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1536 = false ∨ valuation q 1543 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1528)) (literal (valuationOf q) (1540)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 4 (meaning1528 q) (meaning1540 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1540 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1541)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 4 1 (meaning1528 q) (meaning1533 q) (meaning1541 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1533 = false ∨ valuation q 1541 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1542)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 4 2 (meaning1528 q) (meaning1534 q) (meaning1542 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1534 = false ∨ valuation q 1542 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-46, -47, -49, -52]) + (countLit q [-53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -49, -52]) (l₂ := [-53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1543)) (countLit q [-46, -47, -49, -52]) (countLit q [-53, -55, -56, -57]) (count1537 q) 4 3 (meaning1528 q) (meaning1535 q) (meaning1543 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1535 = false ∨ valuation q 1543 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E078.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112078
