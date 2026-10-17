import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1538)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 4 4 (meaning1460 q) (meaning1519 q) (meaning1538 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1519 = false ∨ valuation q 1538 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1539)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 4 5 (meaning1460 q) (meaning1520 q) (meaning1539 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1520 = false ∨ valuation q 1539 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1537)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 5 2 (meaning1461 q) (meaning1517 q) (meaning1537 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1517 = false ∨ valuation q 1537 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1538)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 5 3 (meaning1461 q) (meaning1518 q) (meaning1538 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1518 = false ∨ valuation q 1538 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1539)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 5 4 (meaning1461 q) (meaning1519 q) (meaning1539 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1519 = false ∨ valuation q 1539 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1540)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 5 5 (meaning1461 q) (meaning1520 q) (meaning1540 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1520 = false ∨ valuation q 1540 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1537)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 6 1 (meaning1462 q) (meaning1516 q) (meaning1537 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1516 = false ∨ valuation q 1537 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1538)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 6 2 (meaning1462 q) (meaning1517 q) (meaning1538 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1517 = false ∨ valuation q 1538 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1539)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 6 3 (meaning1462 q) (meaning1518 q) (meaning1539 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1518 = false ∨ valuation q 1539 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1540)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 6 4 (meaning1462 q) (meaning1519 q) (meaning1540 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1519 = false ∨ valuation q 1540 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1540)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 7 3 (meaning1463 q) (meaning1518 q) (meaning1540 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1518 = false ∨ valuation q 1540 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1541)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 8 3 (meaning1464 q) (meaning1518 q) (meaning1541 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1518 = false ∨ valuation q 1541 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1551)) (countLit q [-61]) (countLit q [-62]) (count1551 q) 1 (meaningNeg62 q) (meaning1551 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1551 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1551)) (countLit q [-61]) (countLit q [-62]) (count1551 q) 1 (meaningNeg61 q) (meaning1551 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1551 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1552)) (countLit q [-61]) (countLit q [-62]) (count1551 q) 1 1 (meaningNeg61 q) (meaningNeg62 q) (meaning1552 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 62 = true ∨ valuation q 1552 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (countLit q [-60]) (countLit q [-61, -62]) (count1553 q) 1 (meaning1551 q) (meaning1553 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_right (literal (valuationOf q) (1552)) (literal (valuationOf q) (1554)) (countLit q [-60]) (countLit q [-61, -62]) (count1553 q) 2 (meaning1552 q) (meaning1554 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1554 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1553)) (countLit q [-60]) (countLit q [-61, -62]) (count1553 q) 1 (meaningNeg60 q) (meaning1553 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1553 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (countLit q [-60]) (countLit q [-61, -62]) (count1553 q) 1 1 (meaningNeg60 q) (meaning1551 q) (meaning1554 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1551 = false ∨ valuation q 1554 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1555)) (countLit q [-60]) (countLit q [-61, -62]) (count1553 q) 1 2 (meaningNeg60 q) (meaning1552 q) (meaning1555 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1552 = false ∨ valuation q 1555 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1556)) (countLit q [-63]) (countLit q [-66]) (count1556 q) 1 (meaningNeg66 q) (meaning1556 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1556 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1556)) (countLit q [-63]) (countLit q [-66]) (count1556 q) 1 (meaningNeg63 q) (meaning1556 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1556 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1557 = true := by
  have hs : count1556 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1557)) (countLit q [-63]) (countLit q [-66]) (count1556 q) 1 1 (meaningNeg63 q) (meaningNeg66 q) (meaning1557 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 66 = true ∨ valuation q 1557 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1558)) (countLit q [-69]) (countLit q [-70]) (count1558 q) 1 (meaningNeg70 q) (meaning1558 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1558 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1558)) (countLit q [-69]) (countLit q [-70]) (count1558 q) 1 (meaningNeg69 q) (meaning1558 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1558 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1559)) (countLit q [-69]) (countLit q [-70]) (count1558 q) 1 1 (meaningNeg69 q) (meaningNeg70 q) (meaning1559 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 1559 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 1 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 2 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 1 1 (meaning1556 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1562)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 1 2 (meaning1556 q) (meaning1559 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1559 = false ∨ valuation q 1562 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 2 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E096.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112096
