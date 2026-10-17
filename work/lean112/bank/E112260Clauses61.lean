import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec61 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1953 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 6 4 (meaning1582 q) (meaning1649 q) (meaning1672 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1953 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1649 = false ∨ valuation q 1672 = true := counterClause1953 (baseVal q)

theorem counterClause1954 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 7 3 (meaning1583 q) (meaning1648 q) (meaning1672 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1954 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1648 = false ∨ valuation q 1672 = true := counterClause1954 (baseVal q)

theorem counterClause1955 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1676 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1676)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 7 7 (meaning1583 q) (meaning1652 q) (meaning1676 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1955 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1652 = false ∨ valuation q 1676 = true := counterClause1955 (baseVal q)

theorem counterClause1956 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1678 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1678)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 7 9 (meaning1583 q) (meaning1654 q) (meaning1678 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1956 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1654 = false ∨ valuation q 1678 = true := counterClause1956 (baseVal q)

theorem counterClause1957 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 8 2 (meaning1584 q) (meaning1647 q) (meaning1672 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1957 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1647 = false ∨ valuation q 1672 = true := counterClause1957 (baseVal q)

theorem counterClause1958 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1676 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1676)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 8 6 (meaning1584 q) (meaning1651 q) (meaning1676 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1958 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1651 = false ∨ valuation q 1676 = true := counterClause1958 (baseVal q)

theorem counterClause1959 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1678 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1678)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 8 8 (meaning1584 q) (meaning1653 q) (meaning1678 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1959 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1653 = false ∨ valuation q 1678 = true := counterClause1959 (baseVal q)

theorem counterClause1960 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1679 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1679)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 8 9 (meaning1584 q) (meaning1654 q) (meaning1679 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1960 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1654 = false ∨ valuation q 1679 = true := counterClause1960 (baseVal q)

theorem counterClause1961 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1678 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1678)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 9 7 (meaning1585 q) (meaning1652 q) (meaning1678 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1961 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1652 = false ∨ valuation q 1678 = true := counterClause1961 (baseVal q)

theorem counterClause1962 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1689 = true := by
  have hs : count1689 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1689)) (countLit q [-63]) (countLit q [-66]) (count1689 q) 1 (meaningNeg63 q) (meaning1689 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1962 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1689 = true := counterClause1962 (baseVal q)

theorem counterClause1963 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1690)) (countLit q [-63]) (countLit q [-66]) (count1689 q) 1 1 (meaningNeg63 q) (meaningNeg66 q) (meaning1690 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1963 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 66 = true ∨ valuation q 1690 = true := counterClause1963 (baseVal q)

theorem counterClause1964 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1691)) (countLit q [-70]) (countLit q [-71]) (count1691 q) 1 (meaningNeg71 q) (meaning1691 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1964 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1691 = true := counterClause1964 (baseVal q)

theorem counterClause1965 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1691)) (countLit q [-70]) (countLit q [-71]) (count1691 q) 1 (meaningNeg70 q) (meaning1691 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1965 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1691 = true := counterClause1965 (baseVal q)

theorem counterClause1966 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-63, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1691)) (literal (valuationOf q) (1693)) (countLit q [-63, -66]) (countLit q [-70, -71]) (count1693 q) 1 (meaning1691 q) (meaning1693 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1966 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1693 = true := counterClause1966 (baseVal q)

theorem counterClause1967 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-63, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-70, -71])
  have hm := merge_left (literal (valuationOf q) (1689)) (literal (valuationOf q) (1693)) (countLit q [-63, -66]) (countLit q [-70, -71]) (count1693 q) 1 (meaning1689 q) (meaning1693 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1967 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1693 = true := counterClause1967 (baseVal q)

theorem counterClause1968 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-63, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1694)) (countLit q [-63, -66]) (countLit q [-70, -71]) (count1693 q) 1 1 (meaning1689 q) (meaning1691 q) (meaning1694 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1968 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1691 = false ∨ valuation q 1694 = true := counterClause1968 (baseVal q)

theorem counterClause1969 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-63, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-70, -71])
  have hm := merge_left (literal (valuationOf q) (1690)) (literal (valuationOf q) (1694)) (countLit q [-63, -66]) (countLit q [-70, -71]) (count1693 q) 2 (meaning1690 q) (meaning1694 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1969 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1694 = true := counterClause1969 (baseVal q)

theorem counterClause1970 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1698 = true := by
  have hs : count1697 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1698)) (countLit q [-75]) (countLit q [-77]) (count1697 q) 1 1 (meaningNeg75 q) (meaningNeg77 q) (meaning1698 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1970 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 1698 = true := counterClause1970 (baseVal q)

theorem counterClause1971 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1699)) (countLit q [-78]) (countLit q [-80]) (count1699 q) 1 (meaningNeg80 q) (meaning1699 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1971 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1699 = true := counterClause1971 (baseVal q)

theorem counterClause1972 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1700)) (countLit q [-78]) (countLit q [-80]) (count1699 q) 1 1 (meaningNeg78 q) (meaningNeg80 q) (meaning1700 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1972 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 80 = true ∨ valuation q 1700 = true := counterClause1972 (baseVal q)

theorem counterClause1973 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1702 = true := by
  have hs : count1701 q = (countLit q [-75, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1700)) (literal (valuationOf q) (1702)) (countLit q [-75, -77]) (countLit q [-78, -80]) (count1701 q) 2 (meaning1700 q) (meaning1702 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1973 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1702 = true := counterClause1973 (baseVal q)

theorem counterClause1974 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1703 = true := by
  have hs : count1701 q = (countLit q [-75, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1703)) (countLit q [-75, -77]) (countLit q [-78, -80]) (count1701 q) 2 1 (meaning1698 q) (meaning1699 q) (meaning1703 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1974 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1699 = false ∨ valuation q 1703 = true := counterClause1974 (baseVal q)

theorem counterClause1975 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-75, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1704)) (countLit q [-75, -77]) (countLit q [-78, -80]) (count1701 q) 2 2 (meaning1698 q) (meaning1700 q) (meaning1704 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1975 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1700 = false ∨ valuation q 1704 = true := counterClause1975 (baseVal q)

theorem counterClause1976 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1706 = true := by
  have hs : count1705 q = (countLit q [-63, -66, -70, -71]) + (countLit q [-75, -77, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71]) (l₂ := [-75, -77, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1702)) (literal (valuationOf q) (1706)) (countLit q [-63, -66, -70, -71]) (countLit q [-75, -77, -78, -80]) (count1705 q) 2 (meaning1702 q) (meaning1706 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1976 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1706 = true := counterClause1976 (baseVal q)

theorem counterClause1977 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1707 = true := by
  have hs : count1705 q = (countLit q [-63, -66, -70, -71]) + (countLit q [-75, -77, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71]) (l₂ := [-75, -77, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1707)) (countLit q [-63, -66, -70, -71]) (countLit q [-75, -77, -78, -80]) (count1705 q) 1 2 (meaning1693 q) (meaning1702 q) (meaning1707 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1977 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1702 = false ∨ valuation q 1707 = true := counterClause1977 (baseVal q)

theorem counterClause1978 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1708 = true := by
  have hs : count1705 q = (countLit q [-63, -66, -70, -71]) + (countLit q [-75, -77, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71]) (l₂ := [-75, -77, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1708)) (countLit q [-63, -66, -70, -71]) (countLit q [-75, -77, -78, -80]) (count1705 q) 1 3 (meaning1693 q) (meaning1703 q) (meaning1708 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1978 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1703 = false ∨ valuation q 1708 = true := counterClause1978 (baseVal q)

theorem counterClause1979 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1709 = true := by
  have hs : count1705 q = (countLit q [-63, -66, -70, -71]) + (countLit q [-75, -77, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71]) (l₂ := [-75, -77, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1709)) (countLit q [-63, -66, -70, -71]) (countLit q [-75, -77, -78, -80]) (count1705 q) 1 4 (meaning1693 q) (meaning1704 q) (meaning1709 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1979 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1704 = false ∨ valuation q 1709 = true := counterClause1979 (baseVal q)

theorem counterClause1980 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1709 = true := by
  have hs : count1705 q = (countLit q [-63, -66, -70, -71]) + (countLit q [-75, -77, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71]) (l₂ := [-75, -77, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1709)) (countLit q [-63, -66, -70, -71]) (countLit q [-75, -77, -78, -80]) (count1705 q) 2 3 (meaning1694 q) (meaning1703 q) (meaning1709 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1980 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1703 = false ∨ valuation q 1709 = true := counterClause1980 (baseVal q)

theorem counterClause1981 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1710 = true := by
  have hs : count1705 q = (countLit q [-63, -66, -70, -71]) + (countLit q [-75, -77, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71]) (l₂ := [-75, -77, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1710)) (countLit q [-63, -66, -70, -71]) (countLit q [-75, -77, -78, -80]) (count1705 q) 2 4 (meaning1694 q) (meaning1704 q) (meaning1710 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1981 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1704 = false ∨ valuation q 1710 = true := counterClause1981 (baseVal q)

theorem counterClause1982 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1713 = true := by
  have hs : count1713 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1713)) (countLit q [-83]) (countLit q [-84]) (count1713 q) 1 (meaningNeg83 q) (meaning1713 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1982 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1713 = true := counterClause1982 (baseVal q)

theorem counterClause1983 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1715)) (countLit q [-87]) (countLit q [-88]) (count1715 q) 1 (meaningNeg88 q) (meaning1715 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1983 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1715 = true := counterClause1983 (baseVal q)

theorem counterClause1984 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-83, -84]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1715)) (literal (valuationOf q) (1717)) (countLit q [-83, -84]) (countLit q [-87, -88]) (count1717 q) 1 (meaning1715 q) (meaning1717 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1984 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1717 = true := counterClause1984 (baseVal q)

theorem block61 (q : Snake 81) (h : Conditions q) : B112E260.Block61 (valuation q) :=
  ⟨clause1953 q h, clause1954 q h, clause1955 q h, clause1956 q h, clause1957 q h, clause1958 q h, clause1959 q h, clause1960 q h, clause1961 q h, clause1962 q h, clause1963 q h, clause1964 q h, clause1965 q h, clause1966 q h, clause1967 q h, clause1968 q h, clause1969 q h, clause1970 q h, clause1971 q h, clause1972 q h, clause1973 q h, clause1974 q h, clause1975 q h, clause1976 q h, clause1977 q h, clause1978 q h, clause1979 q h, clause1980 q h, clause1981 q h, clause1982 q h, clause1983 q h, clause1984 q h⟩

end
end Snake9.Regrowth.E112260
