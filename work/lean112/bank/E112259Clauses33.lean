import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 889 = false ∨ valuationOf q 905 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (889)) (literal (valuationOf q) (905)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 1 5 (meaning827 q) (meaning889 q) (meaning905 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 889 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 889 = false ∨ valuation q 905 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 890 = false ∨ valuationOf q 906 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (890)) (literal (valuationOf q) (906)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 1 6 (meaning827 q) (meaning890 q) (meaning906 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 890 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 890 = false ∨ valuation q 906 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 891 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (891)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 1 7 (meaning827 q) (meaning891 q) (meaning907 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 891 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 891 = false ∨ valuation q 907 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 887 = false ∨ valuationOf q 904 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (887)) (literal (valuationOf q) (904)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 2 3 (meaning828 q) (meaning887 q) (meaning904 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 887 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 887 = false ∨ valuation q 904 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 888 = false ∨ valuationOf q 905 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (888)) (literal (valuationOf q) (905)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 2 4 (meaning828 q) (meaning888 q) (meaning905 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 888 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 888 = false ∨ valuation q 905 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 889 = false ∨ valuationOf q 906 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (889)) (literal (valuationOf q) (906)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 2 5 (meaning828 q) (meaning889 q) (meaning906 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 889 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 889 = false ∨ valuation q 906 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 890 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (890)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 2 6 (meaning828 q) (meaning890 q) (meaning907 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 890 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 890 = false ∨ valuation q 907 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 891 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (891)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 2 7 (meaning828 q) (meaning891 q) (meaning908 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 891 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 891 = false ∨ valuation q 908 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 886 = false ∨ valuationOf q 904 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (886)) (literal (valuationOf q) (904)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 3 2 (meaning829 q) (meaning886 q) (meaning904 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 886 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 886 = false ∨ valuation q 904 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 887 = false ∨ valuationOf q 905 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (887)) (literal (valuationOf q) (905)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 3 3 (meaning829 q) (meaning887 q) (meaning905 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 887 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 887 = false ∨ valuation q 905 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 888 = false ∨ valuationOf q 906 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (888)) (literal (valuationOf q) (906)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 3 4 (meaning829 q) (meaning888 q) (meaning906 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 888 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 888 = false ∨ valuation q 906 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 889 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (889)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 3 5 (meaning829 q) (meaning889 q) (meaning907 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 889 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 889 = false ∨ valuation q 907 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 890 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (890)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 3 6 (meaning829 q) (meaning890 q) (meaning908 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 890 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 890 = false ∨ valuation q 908 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 891 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (891)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 3 7 (meaning829 q) (meaning891 q) (meaning909 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 891 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 891 = false ∨ valuation q 909 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 886 = false ∨ valuationOf q 905 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (830)) (literal (valuationOf q) (886)) (literal (valuationOf q) (905)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 4 2 (meaning830 q) (meaning886 q) (meaning905 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 886 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 886 = false ∨ valuation q 905 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 887 = false ∨ valuationOf q 906 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (830)) (literal (valuationOf q) (887)) (literal (valuationOf q) (906)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 4 3 (meaning830 q) (meaning887 q) (meaning906 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 887 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 887 = false ∨ valuation q 906 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 888 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (830)) (literal (valuationOf q) (888)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 4 4 (meaning830 q) (meaning888 q) (meaning907 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 888 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 888 = false ∨ valuation q 907 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 889 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (830)) (literal (valuationOf q) (889)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 4 5 (meaning830 q) (meaning889 q) (meaning908 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 889 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 889 = false ∨ valuation q 908 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 890 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (830)) (literal (valuationOf q) (890)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 4 6 (meaning830 q) (meaning890 q) (meaning909 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 890 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 890 = false ∨ valuation q 909 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 891 = false ∨ valuationOf q 910 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (830)) (literal (valuationOf q) (891)) (literal (valuationOf q) (910)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 4 7 (meaning830 q) (meaning891 q) (meaning910 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 891 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 891 = false ∨ valuation q 910 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 885 = false ∨ valuationOf q 905 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (831)) (literal (valuationOf q) (885)) (literal (valuationOf q) (905)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 5 1 (meaning831 q) (meaning885 q) (meaning905 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 885 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 885 = false ∨ valuation q 905 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 886 = false ∨ valuationOf q 906 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (831)) (literal (valuationOf q) (886)) (literal (valuationOf q) (906)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 5 2 (meaning831 q) (meaning886 q) (meaning906 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 886 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 886 = false ∨ valuation q 906 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 887 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (831)) (literal (valuationOf q) (887)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 5 3 (meaning831 q) (meaning887 q) (meaning907 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 887 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 887 = false ∨ valuation q 907 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 888 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (831)) (literal (valuationOf q) (888)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 5 4 (meaning831 q) (meaning888 q) (meaning908 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 888 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 888 = false ∨ valuation q 908 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 889 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (831)) (literal (valuationOf q) (889)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 5 5 (meaning831 q) (meaning889 q) (meaning909 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 889 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 889 = false ∨ valuation q 909 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 890 = false ∨ valuationOf q 910 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (831)) (literal (valuationOf q) (890)) (literal (valuationOf q) (910)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 5 6 (meaning831 q) (meaning890 q) (meaning910 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 890 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 890 = false ∨ valuation q 910 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 885 = false ∨ valuationOf q 906 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (832)) (literal (valuationOf q) (885)) (literal (valuationOf q) (906)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 6 1 (meaning832 q) (meaning885 q) (meaning906 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 885 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 885 = false ∨ valuation q 906 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 886 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (832)) (literal (valuationOf q) (886)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 6 2 (meaning832 q) (meaning886 q) (meaning907 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 886 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 886 = false ∨ valuation q 907 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 887 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (832)) (literal (valuationOf q) (887)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 6 3 (meaning832 q) (meaning887 q) (meaning908 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 887 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 887 = false ∨ valuation q 908 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 888 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (832)) (literal (valuationOf q) (888)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 6 4 (meaning832 q) (meaning888 q) (meaning909 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 888 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 888 = false ∨ valuation q 909 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 889 = false ∨ valuationOf q 910 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (832)) (literal (valuationOf q) (889)) (literal (valuationOf q) (910)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 6 5 (meaning832 q) (meaning889 q) (meaning910 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 889 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 889 = false ∨ valuation q 910 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 890 = false ∨ valuationOf q 911 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (832)) (literal (valuationOf q) (890)) (literal (valuationOf q) (911)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 6 6 (meaning832 q) (meaning890 q) (meaning911 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 890 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 890 = false ∨ valuation q 911 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E259.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112259
