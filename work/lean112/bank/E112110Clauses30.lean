import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1537)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 3 4 (meaning1459 q) (meaning1519 q) (meaning1537 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1519 = false ∨ valuation q 1537 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1538)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 3 5 (meaning1459 q) (meaning1520 q) (meaning1538 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1520 = false ∨ valuation q 1538 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 3 6 (meaning1459 q) (meaning1521 q) (meaning1539 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1521 = false ∨ valuation q 1539 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 3 7 (meaning1459 q) (meaning1522 q) (meaning1540 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1522 = false ∨ valuation q 1540 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 4 2 (meaning1460 q) (meaning1517 q) (meaning1536 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1517 = false ∨ valuation q 1536 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1537)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 4 3 (meaning1460 q) (meaning1518 q) (meaning1537 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1518 = false ∨ valuation q 1537 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1538)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 4 4 (meaning1460 q) (meaning1519 q) (meaning1538 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1519 = false ∨ valuation q 1538 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 4 5 (meaning1460 q) (meaning1520 q) (meaning1539 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1520 = false ∨ valuation q 1539 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 4 6 (meaning1460 q) (meaning1521 q) (meaning1540 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1521 = false ∨ valuation q 1540 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 5 1 (meaning1461 q) (meaning1516 q) (meaning1536 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1516 = false ∨ valuation q 1536 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1537)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 5 2 (meaning1461 q) (meaning1517 q) (meaning1537 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1517 = false ∨ valuation q 1537 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1538)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 5 3 (meaning1461 q) (meaning1518 q) (meaning1538 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1518 = false ∨ valuation q 1538 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 5 4 (meaning1461 q) (meaning1519 q) (meaning1539 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1519 = false ∨ valuation q 1539 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 5 5 (meaning1461 q) (meaning1520 q) (meaning1540 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1520 = false ∨ valuation q 1540 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 5 6 (meaning1461 q) (meaning1521 q) (meaning1541 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1521 = false ∨ valuation q 1541 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1537)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 6 1 (meaning1462 q) (meaning1516 q) (meaning1537 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1516 = false ∨ valuation q 1537 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1538)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 6 2 (meaning1462 q) (meaning1517 q) (meaning1538 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1517 = false ∨ valuation q 1538 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 6 3 (meaning1462 q) (meaning1518 q) (meaning1539 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1518 = false ∨ valuation q 1539 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 6 4 (meaning1462 q) (meaning1519 q) (meaning1540 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1519 = false ∨ valuation q 1540 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 6 5 (meaning1462 q) (meaning1520 q) (meaning1541 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1520 = false ∨ valuation q 1541 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1538)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 7 1 (meaning1463 q) (meaning1516 q) (meaning1538 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1516 = false ∨ valuation q 1538 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 7 2 (meaning1463 q) (meaning1517 q) (meaning1539 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1517 = false ∨ valuation q 1539 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 7 3 (meaning1463 q) (meaning1518 q) (meaning1540 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1518 = false ∨ valuation q 1540 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 7 4 (meaning1463 q) (meaning1519 q) (meaning1541 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1519 = false ∨ valuation q 1541 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1542)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 7 5 (meaning1463 q) (meaning1520 q) (meaning1542 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1520 = false ∨ valuation q 1542 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1464)) (literal (valuationOf q) (1538)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 8 (meaning1464 q) (meaning1538 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1538 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 8 1 (meaning1464 q) (meaning1516 q) (meaning1539 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1516 = false ∨ valuation q 1539 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 8 2 (meaning1464 q) (meaning1517 q) (meaning1540 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1517 = false ∨ valuation q 1540 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 8 3 (meaning1464 q) (meaning1518 q) (meaning1541 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1518 = false ∨ valuation q 1541 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1542)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 8 4 (meaning1464 q) (meaning1519 q) (meaning1542 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1519 = false ∨ valuation q 1542 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 9 1 (meaning1465 q) (meaning1516 q) (meaning1540 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1516 = false ∨ valuation q 1540 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1551)) (countLit q [-61]) (countLit q [-63]) (count1551 q) 1 (meaningNeg63 q) (meaning1551 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1551 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E110.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112110
