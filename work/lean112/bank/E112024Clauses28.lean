import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1510)) (countLit q [-36]) (countLit q [-37]) (count1510 q) 1 (meaningNeg37 q) (meaning1510 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1510 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1510)) (countLit q [-36]) (countLit q [-37]) (count1510 q) 1 (meaningNeg36 q) (meaning1510 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1510 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1511)) (countLit q [-36]) (countLit q [-37]) (count1510 q) 1 1 (meaningNeg36 q) (meaningNeg37 q) (meaning1511 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 1511 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1512)) (countLit q [-39]) (countLit q [-41]) (count1512 q) 1 (meaningNeg41 q) (meaning1512 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1512 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1512)) (countLit q [-39]) (countLit q [-41]) (count1512 q) 1 (meaningNeg39 q) (meaning1512 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1512 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1513)) (countLit q [-39]) (countLit q [-41]) (count1512 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1513 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1513 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 2 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 1 (meaning1510 q) (meaning1512 q) (meaning1515 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1516)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 2 (meaning1510 q) (meaning1513 q) (meaning1516 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1513 = false ∨ valuation q 1516 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1516)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 2 1 (meaning1511 q) (meaning1512 q) (meaning1516 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1512 = false ∨ valuation q 1516 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_right (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_right (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 3 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 1 (meaning1506 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1520)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 2 (meaning1506 q) (meaning1515 q) (meaning1520 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1515 = false ∨ valuation q 1520 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1521)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 3 (meaning1506 q) (meaning1516 q) (meaning1521 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1516 = false ∨ valuation q 1521 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 1 (meaning1507 q) (meaning1514 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1514 = false ∨ valuation q 1520 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1521)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 2 (meaning1507 q) (meaning1515 q) (meaning1521 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1515 = false ∨ valuation q 1521 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1522)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 3 (meaning1507 q) (meaning1516 q) (meaning1522 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1516 = false ∨ valuation q 1522 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1521)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 3 1 (meaning1508 q) (meaning1514 q) (meaning1521 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1514 = false ∨ valuation q 1521 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1522)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 3 2 (meaning1508 q) (meaning1515 q) (meaning1522 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1515 = false ∨ valuation q 1522 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1523 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1523)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 3 3 (meaning1508 q) (meaning1516 q) (meaning1523 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1516 = false ∨ valuation q 1523 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1522)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 4 1 (meaning1509 q) (meaning1514 q) (meaning1522 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1514 = false ∨ valuation q 1522 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1523 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1523)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 4 2 (meaning1509 q) (meaning1515 q) (meaning1523 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1515 = false ∨ valuation q 1523 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1526)) (countLit q [-43]) (countLit q [-44]) (count1526 q) 1 (meaningNeg44 q) (meaning1526 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1526 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1526)) (countLit q [-43]) (countLit q [-44]) (count1526 q) 1 (meaningNeg43 q) (meaning1526 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1526 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1527)) (countLit q [-43]) (countLit q [-44]) (count1526 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning1527 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 1527 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1528)) (countLit q [-47]) (countLit q [-50]) (count1528 q) 1 (meaningNeg50 q) (meaning1528 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1528 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1528)) (countLit q [-47]) (countLit q [-50]) (count1528 q) 1 (meaningNeg47 q) (meaning1528 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1528 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E024.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112024
