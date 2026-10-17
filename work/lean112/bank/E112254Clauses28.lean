import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1508)) (countLit q [-14]) (countLit q [-15]) (count1508 q) 1 (meaningNeg15 q) (meaning1508 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1508 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1508)) (countLit q [-14]) (countLit q [-15]) (count1508 q) 1 (meaningNeg14 q) (meaning1508 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1508 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1509)) (countLit q [-14]) (countLit q [-15]) (count1508 q) 1 1 (meaningNeg14 q) (meaningNeg15 q) (meaning1509 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 1509 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1510)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 1 (meaning1508 q) (meaning1510 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1510 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1511)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 2 (meaning1509 q) (meaning1511 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1511 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_left (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 1 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1511)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 1 1 (meaning1506 q) (meaning1508 q) (meaning1511 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = false ∨ valuation q 1511 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1512)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 1 2 (meaning1506 q) (meaning1509 q) (meaning1512 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1509 = false ∨ valuation q 1512 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 2 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 2 1 (meaning1507 q) (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1508 = false ∨ valuation q 1512 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-9, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-9, -12]) (countLit q [-14, -15]) (count1510 q) 2 2 (meaning1507 q) (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = false ∨ valuation q 1513 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1514)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 1 (meaning1503 q) (meaning1514 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1514 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 1 1 (meaning1503 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 1 2 (meaning1503 q) (meaning1511 q) (meaning1516 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1511 = false ∨ valuation q 1516 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 1 3 (meaning1503 q) (meaning1512 q) (meaning1517 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1512 = false ∨ valuation q 1517 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 1 4 (meaning1503 q) (meaning1513 q) (meaning1518 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1513 = false ∨ valuation q 1518 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 2 (meaning1504 q) (meaning1515 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1515 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 2 1 (meaning1504 q) (meaning1510 q) (meaning1516 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1510 = false ∨ valuation q 1516 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 2 2 (meaning1504 q) (meaning1511 q) (meaning1517 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1511 = false ∨ valuation q 1517 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 2 3 (meaning1504 q) (meaning1512 q) (meaning1518 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1512 = false ∨ valuation q 1518 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 2 4 (meaning1504 q) (meaning1513 q) (meaning1519 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1513 = false ∨ valuation q 1519 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 3 (meaning1505 q) (meaning1516 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1516 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 3 1 (meaning1505 q) (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1510 = false ∨ valuation q 1517 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 3 2 (meaning1505 q) (meaning1511 q) (meaning1518 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1511 = false ∨ valuation q 1518 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1519 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -12, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -8]) (countLit q [-9, -12, -14, -15]) (count1514 q) 3 3 (meaning1505 q) (meaning1512 q) (meaning1519 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1512 = false ∨ valuation q 1519 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-19]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1521)) (countLit q [-19]) (countLit q [-22]) (count1521 q) 1 (meaningNeg22 q) (meaning1521 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1521 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-19]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1521)) (countLit q [-19]) (countLit q [-22]) (count1521 q) 1 (meaningNeg19 q) (meaning1521 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1521 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-19]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1522)) (countLit q [-19]) (countLit q [-22]) (count1521 q) 1 1 (meaningNeg19 q) (meaningNeg22 q) (meaning1522 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 22 = true ∨ valuation q 1522 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -22])
  have hm := merge_right (literal (valuationOf q) (1521)) (literal (valuationOf q) (1523)) (countLit q [-18]) (countLit q [-19, -22]) (count1523 q) 1 (meaning1521 q) (meaning1523 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1523 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -22])
  have hm := merge_right (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (countLit q [-18]) (countLit q [-19, -22]) (count1523 q) 2 (meaning1522 q) (meaning1524 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -22])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1523)) (countLit q [-18]) (countLit q [-19, -22]) (count1523 q) 1 (meaningNeg18 q) (meaning1523 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1523 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1521 = false ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -22])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1524)) (countLit q [-18]) (countLit q [-19, -22]) (count1523 q) 1 1 (meaningNeg18 q) (meaning1521 q) (meaning1524 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1521 = false ∨ valuation q 1524 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E254.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112254
