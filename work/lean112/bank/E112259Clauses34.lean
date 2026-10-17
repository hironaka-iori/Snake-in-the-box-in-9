import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 885 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (833)) (literal (valuationOf q) (885)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 7 1 (meaning833 q) (meaning885 q) (meaning907 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 885 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 885 = false ∨ valuation q 907 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 886 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (833)) (literal (valuationOf q) (886)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 7 2 (meaning833 q) (meaning886 q) (meaning908 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 886 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 886 = false ∨ valuation q 908 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 887 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (833)) (literal (valuationOf q) (887)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 7 3 (meaning833 q) (meaning887 q) (meaning909 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 887 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 887 = false ∨ valuation q 909 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 888 = false ∨ valuationOf q 910 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (833)) (literal (valuationOf q) (888)) (literal (valuationOf q) (910)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 7 4 (meaning833 q) (meaning888 q) (meaning910 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 888 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 888 = false ∨ valuation q 910 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 889 = false ∨ valuationOf q 911 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (833)) (literal (valuationOf q) (889)) (literal (valuationOf q) (911)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 7 5 (meaning833 q) (meaning889 q) (meaning911 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 889 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 889 = false ∨ valuation q 911 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 890 = false ∨ valuationOf q 912 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (833)) (literal (valuationOf q) (890)) (literal (valuationOf q) (912)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 7 6 (meaning833 q) (meaning890 q) (meaning912 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 890 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 890 = false ∨ valuation q 912 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 885 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (885)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 8 1 (meaning834 q) (meaning885 q) (meaning908 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 885 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 885 = false ∨ valuation q 908 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 886 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (886)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 8 2 (meaning834 q) (meaning886 q) (meaning909 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 886 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 886 = false ∨ valuation q 909 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 887 = false ∨ valuationOf q 910 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (887)) (literal (valuationOf q) (910)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 8 3 (meaning834 q) (meaning887 q) (meaning910 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 887 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 887 = false ∨ valuation q 910 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 888 = false ∨ valuationOf q 911 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (888)) (literal (valuationOf q) (911)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 8 4 (meaning834 q) (meaning888 q) (meaning911 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 888 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 888 = false ∨ valuation q 911 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 889 = false ∨ valuationOf q 912 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (889)) (literal (valuationOf q) (912)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 8 5 (meaning834 q) (meaning889 q) (meaning912 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 889 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 889 = false ∨ valuation q 912 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 885 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (885)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 9 1 (meaning835 q) (meaning885 q) (meaning909 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 885 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 885 = false ∨ valuation q 909 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 886 = false ∨ valuationOf q 910 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (886)) (literal (valuationOf q) (910)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 9 2 (meaning835 q) (meaning886 q) (meaning910 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 886 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 886 = false ∨ valuation q 910 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 887 = false ∨ valuationOf q 911 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (887)) (literal (valuationOf q) (911)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 9 3 (meaning835 q) (meaning887 q) (meaning911 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 887 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 887 = false ∨ valuation q 911 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 888 = false ∨ valuationOf q 912 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (888)) (literal (valuationOf q) (912)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 9 4 (meaning835 q) (meaning888 q) (meaning912 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 888 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 888 = false ∨ valuation q 912 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_left (literal (valuationOf q) (836)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 10 (meaning836 q) (meaning909 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 909 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 885 = false ∨ valuationOf q 910 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (885)) (literal (valuationOf q) (910)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 10 1 (meaning836 q) (meaning885 q) (meaning910 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 885 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 885 = false ∨ valuation q 910 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 886 = false ∨ valuationOf q 911 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (886)) (literal (valuationOf q) (911)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 10 2 (meaning836 q) (meaning886 q) (meaning911 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 886 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 886 = false ∨ valuation q 911 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 885 = false ∨ valuationOf q 911 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (885)) (literal (valuationOf q) (911)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 11 1 (meaning837 q) (meaning885 q) (meaning911 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 885 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 885 = false ∨ valuation q 911 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 918 = true := by
  have hs : count918 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (918)) (countLit q [-63]) (countLit q [-64]) (count918 q) 1 (meaningNeg64 q) (meaning918 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 918 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 918 = true := by
  have hs : count918 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (918)) (countLit q [-63]) (countLit q [-64]) (count918 q) 1 (meaningNeg63 q) (meaning918 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 918 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 64 = true ∨ valuationOf q 919 = true := by
  have hs : count918 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (919)) (countLit q [-63]) (countLit q [-64]) (count918 q) 1 1 (meaningNeg63 q) (meaningNeg64 q) (meaning919 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 64 = true ∨ valuation q 919 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 920 = true := by
  have hs : count920 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_right (literal (valuationOf q) (918)) (literal (valuationOf q) (920)) (countLit q [-62]) (countLit q [-63, -64]) (count920 q) 1 (meaning918 q) (meaning920 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 920 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 921 = true := by
  have hs : count920 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_right (literal (valuationOf q) (919)) (literal (valuationOf q) (921)) (countLit q [-62]) (countLit q [-63, -64]) (count920 q) 2 (meaning919 q) (meaning921 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 921 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 920 = true := by
  have hs : count920 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (920)) (countLit q [-62]) (countLit q [-63, -64]) (count920 q) 1 (meaningNeg62 q) (meaning920 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 920 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 918 = false ∨ valuationOf q 921 = true := by
  have hs : count920 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (918)) (literal (valuationOf q) (921)) (countLit q [-62]) (countLit q [-63, -64]) (count920 q) 1 1 (meaningNeg62 q) (meaning918 q) (meaning921 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 918 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 918 = false ∨ valuation q 921 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 919 = false ∨ valuationOf q 922 = true := by
  have hs : count920 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (919)) (literal (valuationOf q) (922)) (countLit q [-62]) (countLit q [-63, -64]) (count920 q) 1 2 (meaningNeg62 q) (meaning919 q) (meaning922 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 919 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 919 = false ∨ valuation q 922 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 923 = true := by
  have hs : count923 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (923)) (countLit q [-66]) (countLit q [-68]) (count923 q) 1 (meaningNeg68 q) (meaning923 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 923 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 923 = true := by
  have hs : count923 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (923)) (countLit q [-66]) (countLit q [-68]) (count923 q) 1 (meaningNeg66 q) (meaning923 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 923 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 68 = true ∨ valuationOf q 924 = true := by
  have hs : count923 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (924)) (countLit q [-66]) (countLit q [-68]) (count923 q) 1 1 (meaningNeg66 q) (meaningNeg68 q) (meaning924 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 924 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 925 = true := by
  have hs : count925 q = (countLit q [-69]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (925)) (countLit q [-69]) (countLit q [-74]) (count925 q) 1 (meaningNeg74 q) (meaning925 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 925 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 925 = true := by
  have hs : count925 q = (countLit q [-69]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (925)) (countLit q [-69]) (countLit q [-74]) (count925 q) 1 (meaningNeg69 q) (meaning925 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 925 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E259.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112259
