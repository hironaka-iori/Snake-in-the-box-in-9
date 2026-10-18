import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1001 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (915)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1001)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 5 6 (meaning915 q) (meaning980 q) (meaning1001 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 980 = false ∨ valuation q 1001 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1002 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (915)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1002)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 5 7 (meaning915 q) (meaning981 q) (meaning1002 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 981 = false ∨ valuation q 1002 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1003 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (915)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1003)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 5 8 (meaning915 q) (meaning982 q) (meaning1003 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 982 = false ∨ valuation q 1003 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1004 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (915)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 5 9 (meaning915 q) (meaning983 q) (meaning1004 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 983 = false ∨ valuation q 1004 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1000 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1000)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 6 4 (meaning916 q) (meaning978 q) (meaning1000 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 978 = false ∨ valuation q 1000 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1001 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1001)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 6 5 (meaning916 q) (meaning979 q) (meaning1001 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 979 = false ∨ valuation q 1001 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1002 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1002)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 6 6 (meaning916 q) (meaning980 q) (meaning1002 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 980 = false ∨ valuation q 1002 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1003 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1003)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 6 7 (meaning916 q) (meaning981 q) (meaning1003 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 981 = false ∨ valuation q 1003 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1004 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 6 8 (meaning916 q) (meaning982 q) (meaning1004 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 982 = false ∨ valuation q 1004 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1005 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1005)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 6 9 (meaning916 q) (meaning983 q) (meaning1005 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 983 = false ∨ valuation q 1005 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1001 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1001)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 7 4 (meaning917 q) (meaning978 q) (meaning1001 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 978 = false ∨ valuation q 1001 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1002 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1002)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 7 5 (meaning917 q) (meaning979 q) (meaning1002 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 979 = false ∨ valuation q 1002 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1003 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1003)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 7 6 (meaning917 q) (meaning980 q) (meaning1003 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 980 = false ∨ valuation q 1003 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1004 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 7 7 (meaning917 q) (meaning981 q) (meaning1004 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 981 = false ∨ valuation q 1004 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1005 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1005)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 7 8 (meaning917 q) (meaning982 q) (meaning1005 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 982 = false ∨ valuation q 1005 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1006)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 7 9 (meaning917 q) (meaning983 q) (meaning1006 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 983 = false ∨ valuation q 1006 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1007 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (984)) (literal (valuationOf q) (1007)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 7 10 (meaning917 q) (meaning984 q) (meaning1007 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 984 = false ∨ valuation q 1007 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1002 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1002)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 8 4 (meaning918 q) (meaning978 q) (meaning1002 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 978 = false ∨ valuation q 1002 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1003 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1003)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 8 5 (meaning918 q) (meaning979 q) (meaning1003 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 979 = false ∨ valuation q 1003 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1004 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 8 6 (meaning918 q) (meaning980 q) (meaning1004 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 980 = false ∨ valuation q 1004 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1005 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1005)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 8 7 (meaning918 q) (meaning981 q) (meaning1005 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 981 = false ∨ valuation q 1005 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1006)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 8 8 (meaning918 q) (meaning982 q) (meaning1006 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 982 = false ∨ valuation q 1006 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1007 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1007)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 8 9 (meaning918 q) (meaning983 q) (meaning1007 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 983 = false ∨ valuation q 1007 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 977 = false ∨ valuationOf q 1002 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (977)) (literal (valuationOf q) (1002)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 9 3 (meaning919 q) (meaning977 q) (meaning1002 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 977 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 977 = false ∨ valuation q 1002 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1003 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1003)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 9 4 (meaning919 q) (meaning978 q) (meaning1003 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 978 = false ∨ valuation q 1003 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1004 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 9 5 (meaning919 q) (meaning979 q) (meaning1004 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 979 = false ∨ valuation q 1004 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1005 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1005)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 9 6 (meaning919 q) (meaning980 q) (meaning1005 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 980 = false ∨ valuation q 1005 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1006)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 9 7 (meaning919 q) (meaning981 q) (meaning1006 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 981 = false ∨ valuation q 1006 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1007 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1007)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 9 8 (meaning919 q) (meaning982 q) (meaning1007 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 982 = false ∨ valuation q 1007 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1008 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1008)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 9 9 (meaning919 q) (meaning983 q) (meaning1008 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 983 = false ∨ valuation q 1008 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1004 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 10 4 (meaning920 q) (meaning978 q) (meaning1004 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 978 = false ∨ valuation q 1004 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1005 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1005)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 10 5 (meaning920 q) (meaning979 q) (meaning1005 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 979 = false ∨ valuation q 1005 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E121.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112121
