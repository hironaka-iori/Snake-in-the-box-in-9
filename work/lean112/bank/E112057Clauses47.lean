import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 972 = false ∨ valuationOf q 986 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (972)) (literal (valuationOf q) (986)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 6 2 (meaning952 q) (meaning972 q) (meaning986 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 972 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 972 = false ∨ valuation q 986 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 973 = false ∨ valuationOf q 987 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (973)) (literal (valuationOf q) (987)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 6 3 (meaning952 q) (meaning973 q) (meaning987 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 973 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 973 = false ∨ valuation q 987 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 974 = false ∨ valuationOf q 988 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (974)) (literal (valuationOf q) (988)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 6 4 (meaning952 q) (meaning974 q) (meaning988 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 974 = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 974 = false ∨ valuation q 988 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 976 = false ∨ valuationOf q 990 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (976)) (literal (valuationOf q) (990)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 6 6 (meaning952 q) (meaning976 q) (meaning990 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 976 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 976 = false ∨ valuation q 990 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 974 = false ∨ valuationOf q 990 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (974)) (literal (valuationOf q) (990)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 8 4 (meaning954 q) (meaning974 q) (meaning990 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 974 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 974 = false ∨ valuation q 990 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1004 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (986)) (literal (valuationOf q) (1004)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 2 8 (meaning916 q) (meaning986 q) (meaning1004 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 986 = false ∨ valuation q 1004 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1005 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (987)) (literal (valuationOf q) (1005)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 2 9 (meaning916 q) (meaning987 q) (meaning1005 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 987 = false ∨ valuation q 1005 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1003 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (984)) (literal (valuationOf q) (1003)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 3 6 (meaning917 q) (meaning984 q) (meaning1003 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 984 = false ∨ valuation q 1003 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1004 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (985)) (literal (valuationOf q) (1004)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 3 7 (meaning917 q) (meaning985 q) (meaning1004 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 985 = false ∨ valuation q 1004 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1005 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (986)) (literal (valuationOf q) (1005)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 3 8 (meaning917 q) (meaning986 q) (meaning1005 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 986 = false ∨ valuation q 1005 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1006 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (987)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 3 9 (meaning917 q) (meaning987 q) (meaning1006 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 987 = false ∨ valuation q 1006 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 990 = false ∨ valuationOf q 1009 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (990)) (literal (valuationOf q) (1009)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 3 12 (meaning917 q) (meaning990 q) (meaning1009 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 990 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 990 = false ∨ valuation q 1009 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1004 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (984)) (literal (valuationOf q) (1004)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 4 6 (meaning918 q) (meaning984 q) (meaning1004 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 984 = false ∨ valuation q 1004 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1005 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (985)) (literal (valuationOf q) (1005)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 4 7 (meaning918 q) (meaning985 q) (meaning1005 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 985 = false ∨ valuation q 1005 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1006 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (986)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 4 8 (meaning918 q) (meaning986 q) (meaning1006 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 986 = false ∨ valuation q 1006 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1007 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (987)) (literal (valuationOf q) (1007)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 4 9 (meaning918 q) (meaning987 q) (meaning1007 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 987 = false ∨ valuation q 1007 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 988 = false ∨ valuationOf q 1008 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (988)) (literal (valuationOf q) (1008)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 4 10 (meaning918 q) (meaning988 q) (meaning1008 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 988 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 988 = false ∨ valuation q 1008 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1004 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1004)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 5 5 (meaning919 q) (meaning983 q) (meaning1004 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 983 = false ∨ valuation q 1004 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1005 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (984)) (literal (valuationOf q) (1005)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 5 6 (meaning919 q) (meaning984 q) (meaning1005 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 984 = false ∨ valuation q 1005 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1006 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (985)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 5 7 (meaning919 q) (meaning985 q) (meaning1006 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 985 = false ∨ valuation q 1006 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1007 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (986)) (literal (valuationOf q) (1007)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 5 8 (meaning919 q) (meaning986 q) (meaning1007 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 986 = false ∨ valuation q 1007 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1008 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (987)) (literal (valuationOf q) (1008)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 5 9 (meaning919 q) (meaning987 q) (meaning1008 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 987 = false ∨ valuation q 1008 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1004 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1004)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 6 4 (meaning920 q) (meaning982 q) (meaning1004 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 982 = false ∨ valuation q 1004 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1005 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1005)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 6 5 (meaning920 q) (meaning983 q) (meaning1005 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 983 = false ∨ valuation q 1005 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1006 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (984)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 6 6 (meaning920 q) (meaning984 q) (meaning1006 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 984 = false ∨ valuation q 1006 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1007 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (985)) (literal (valuationOf q) (1007)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 6 7 (meaning920 q) (meaning985 q) (meaning1007 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 985 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 985 = false ∨ valuation q 1007 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1008 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (986)) (literal (valuationOf q) (1008)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 6 8 (meaning920 q) (meaning986 q) (meaning1008 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 986 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 986 = false ∨ valuation q 1008 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1009 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (987)) (literal (valuationOf q) (1009)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 6 9 (meaning920 q) (meaning987 q) (meaning1009 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 987 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 987 = false ∨ valuation q 1009 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1005 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1005)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 7 4 (meaning921 q) (meaning982 q) (meaning1005 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 982 = false ∨ valuation q 1005 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1006 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 7 5 (meaning921 q) (meaning983 q) (meaning1006 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 983 = false ∨ valuation q 1006 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1007 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (984)) (literal (valuationOf q) (1007)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 7 6 (meaning921 q) (meaning984 q) (meaning1007 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 984 = false ∨ valuation q 1007 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1005 = true := by
  have hs : count995 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) + (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (l₂ := [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1005)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (count995 q) 8 3 (meaning922 q) (meaning981 q) (meaning1005 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 981 = false ∨ valuation q 1005 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E057.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112057
