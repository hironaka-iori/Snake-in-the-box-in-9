import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1516 = true := by
  have hs : count1515 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1516)) (countLit q [-78]) (countLit q [-79]) (count1515 q) 1 1 (meaningNeg78 q) (meaningNeg79 q) (meaning1516 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 1516 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1517)) (countLit q [-83]) (countLit q [-85]) (count1517 q) 1 (meaningNeg85 q) (meaning1517 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1517 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1517)) (countLit q [-83]) (countLit q [-85]) (count1517 q) 1 (meaningNeg83 q) (meaning1517 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1517 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1518)) (countLit q [-83]) (countLit q [-85]) (count1517 q) 1 1 (meaningNeg83 q) (meaningNeg85 q) (meaning1518 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 1518 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (1517)) (literal (valuationOf q) (1519)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 1 (meaning1517 q) (meaning1519 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1519 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 2 (meaning1518 q) (meaning1520 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_left (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 1 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1520)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 1 1 (meaning1515 q) (meaning1517 q) (meaning1520 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1517 = false ∨ valuation q 1520 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1521)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 1 2 (meaning1515 q) (meaning1518 q) (meaning1521 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1518 = false ∨ valuation q 1521 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_left (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 2 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1521)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 2 1 (meaning1516 q) (meaning1517 q) (meaning1521 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1517 = false ∨ valuation q 1521 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1522 = true := by
  have hs : count1519 q = (countLit q [-78, -79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -79]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1522)) (countLit q [-78, -79]) (countLit q [-83, -85]) (count1519 q) 2 2 (meaning1516 q) (meaning1518 q) (meaning1522 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1518 = false ∨ valuation q 1522 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1523)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 1 (meaning1519 q) (meaning1523 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1523 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1524)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 2 (meaning1520 q) (meaning1524 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1524 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1525 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1521)) (literal (valuationOf q) (1525)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 3 (meaning1521 q) (meaning1525 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1512)) (literal (valuationOf q) (1523)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 1 (meaning1512 q) (meaning1523 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1523 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1524)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 1 1 (meaning1512 q) (meaning1519 q) (meaning1524 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1519 = false ∨ valuation q 1524 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1525)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 1 2 (meaning1512 q) (meaning1520 q) (meaning1525 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1520 = false ∨ valuation q 1525 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1526 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1526)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 1 3 (meaning1512 q) (meaning1521 q) (meaning1526 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1521 = false ∨ valuation q 1526 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1527 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1527)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 1 4 (meaning1512 q) (meaning1522 q) (meaning1527 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1522 = false ∨ valuation q 1527 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1513)) (literal (valuationOf q) (1524)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 2 (meaning1513 q) (meaning1524 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1524 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1525 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1525)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 2 1 (meaning1513 q) (meaning1519 q) (meaning1525 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1519 = false ∨ valuation q 1525 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1526 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1526)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 2 2 (meaning1513 q) (meaning1520 q) (meaning1526 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1520 = false ∨ valuation q 1526 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1527 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1527)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 2 3 (meaning1513 q) (meaning1521 q) (meaning1527 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1521 = false ∨ valuation q 1527 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1525 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1514)) (literal (valuationOf q) (1525)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 3 (meaning1514 q) (meaning1525 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1525 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1526 = true := by
  have hs : count1523 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1526)) (countLit q [-72, -76, -77]) (countLit q [-78, -79, -83, -85]) (count1523 q) 3 1 (meaning1514 q) (meaning1519 q) (meaning1526 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1519 = false ∨ valuation q 1526 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1531)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 2 (meaning1524 q) (meaning1531 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1531 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1525)) (literal (valuationOf q) (1532)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 3 (meaning1525 q) (meaning1532 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1532 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1533)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 4 (meaning1526 q) (meaning1533 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1533 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1531)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 1 1 (meaning1503 q) (meaning1523 q) (meaning1531 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1523 = false ∨ valuation q 1531 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1532)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 1 2 (meaning1503 q) (meaning1524 q) (meaning1532 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1524 = false ∨ valuation q 1532 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1533)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 1 3 (meaning1503 q) (meaning1525 q) (meaning1533 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1525 = false ∨ valuation q 1533 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E171.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112171
