import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1006)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 10 6 (meaning920 q) (meaning980 q) (meaning1006 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 980 = false ∨ valuation q 1006 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1007 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1007)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 10 7 (meaning920 q) (meaning981 q) (meaning1007 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 981 = false ∨ valuation q 1007 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1008 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1008)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 10 8 (meaning920 q) (meaning982 q) (meaning1008 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 982 = false ∨ valuation q 1008 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1005 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1005)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 11 4 (meaning921 q) (meaning978 q) (meaning1005 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 978 = false ∨ valuation q 1005 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1006)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 11 5 (meaning921 q) (meaning979 q) (meaning1006 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 979 = false ∨ valuation q 1006 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1007 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1007)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 11 6 (meaning921 q) (meaning980 q) (meaning1007 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 980 = false ∨ valuation q 1007 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1008 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1008)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 11 7 (meaning921 q) (meaning981 q) (meaning1008 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 981 = false ∨ valuation q 1008 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1006)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 12 4 (meaning922 q) (meaning978 q) (meaning1006 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 978 = false ∨ valuation q 1006 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1007 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1007)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 12 5 (meaning922 q) (meaning979 q) (meaning1007 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 979 = false ∨ valuation q 1007 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1007 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1007)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 13 4 (meaning923 q) (meaning978 q) (meaning1007 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 978 = false ∨ valuation q 1007 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1015 = true := by
  have hs : count1015 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1015)) (countLit q [-63]) (countLit q [-66]) (count1015 q) 1 (meaningNeg66 q) (meaning1015 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1015 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1015 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1017 = true := by
  have hs : count1017 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1017)) (countLit q [-68]) (countLit q [-69]) (count1017 q) 1 (meaningNeg69 q) (meaning1017 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1017 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1017 = true := by
  have hs : count1017 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1017)) (countLit q [-68]) (countLit q [-69]) (count1017 q) 1 (meaningNeg68 q) (meaning1017 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1017 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1018 = true := by
  have hs : count1017 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1018)) (countLit q [-68]) (countLit q [-69]) (count1017 q) 1 1 (meaningNeg68 q) (meaningNeg69 q) (meaning1018 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 1018 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1019 = true := by
  have hs : count1019 q = (countLit q [-63, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (1017)) (literal (valuationOf q) (1019)) (countLit q [-63, -66]) (countLit q [-68, -69]) (count1019 q) 1 (meaning1017 q) (meaning1019 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1019 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1020 = true := by
  have hs : count1019 q = (countLit q [-63, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (1018)) (literal (valuationOf q) (1020)) (countLit q [-63, -66]) (countLit q [-68, -69]) (count1019 q) 2 (meaning1018 q) (meaning1020 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1020 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1019 = true := by
  have hs : count1019 q = (countLit q [-63, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-68, -69])
  have hm := merge_left (literal (valuationOf q) (1015)) (literal (valuationOf q) (1019)) (countLit q [-63, -66]) (countLit q [-68, -69]) (count1019 q) 1 (meaning1015 q) (meaning1019 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1019 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1017 = false ∨ valuationOf q 1020 = true := by
  have hs : count1019 q = (countLit q [-63, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1015)) (literal (valuationOf q) (1017)) (literal (valuationOf q) (1020)) (countLit q [-63, -66]) (countLit q [-68, -69]) (count1019 q) 1 1 (meaning1015 q) (meaning1017 q) (meaning1020 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1017 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1017 = false ∨ valuation q 1020 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true := by
  have hs : count1019 q = (countLit q [-63, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1015)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1021)) (countLit q [-63, -66]) (countLit q [-68, -69]) (count1019 q) 1 2 (meaning1015 q) (meaning1018 q) (meaning1021 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1018 = false ∨ valuation q 1021 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1023 = true := by
  have hs : count1023 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1023)) (countLit q [-71]) (countLit q [-74]) (count1023 q) 1 (meaningNeg74 q) (meaning1023 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1023 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1023 = true := by
  have hs : count1023 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1023)) (countLit q [-71]) (countLit q [-74]) (count1023 q) 1 (meaningNeg71 q) (meaning1023 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1023 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1024 = true := by
  have hs : count1023 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1024)) (countLit q [-71]) (countLit q [-74]) (count1023 q) 1 1 (meaningNeg71 q) (meaningNeg74 q) (meaning1024 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 74 = true ∨ valuation q 1024 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1025 = true := by
  have hs : count1025 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1025)) (countLit q [-77]) (countLit q [-78]) (count1025 q) 1 (meaningNeg78 q) (meaning1025 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1025 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1025 = true := by
  have hs : count1025 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1025)) (countLit q [-77]) (countLit q [-78]) (count1025 q) 1 (meaningNeg77 q) (meaning1025 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1025 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1026 = true := by
  have hs : count1025 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1026)) (countLit q [-77]) (countLit q [-78]) (count1025 q) 1 1 (meaningNeg77 q) (meaningNeg78 q) (meaning1026 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 78 = true ∨ valuation q 1026 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1027 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1025)) (literal (valuationOf q) (1027)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 1 (meaning1025 q) (meaning1027 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1027 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1028 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1026)) (literal (valuationOf q) (1028)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 2 (meaning1026 q) (meaning1028 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1028 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1027 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1023)) (literal (valuationOf q) (1027)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 1 (meaning1023 q) (meaning1027 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1027 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1028 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1023)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1028)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 1 1 (meaning1023 q) (meaning1025 q) (meaning1028 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1025 = false ∨ valuation q 1028 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1029 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1023)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1029)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 1 2 (meaning1023 q) (meaning1026 q) (meaning1029 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1026 = false ∨ valuation q 1029 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1028 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1024)) (literal (valuationOf q) (1028)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 2 (meaning1024 q) (meaning1028 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1028 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1029 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1029)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 2 1 (meaning1024 q) (meaning1025 q) (meaning1029 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1025 = false ∨ valuation q 1029 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E121.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112121
