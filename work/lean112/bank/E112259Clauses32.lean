import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 873 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (873)) (literal (valuationOf q) (879)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 2 1 (meaning866 q) (meaning873 q) (meaning879 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 873 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 873 = false ∨ valuation q 879 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 874 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (874)) (literal (valuationOf q) (880)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 2 2 (meaning866 q) (meaning874 q) (meaning880 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 874 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 874 = false ∨ valuation q 880 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (875)) (literal (valuationOf q) (881)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 2 3 (meaning866 q) (meaning875 q) (meaning881 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 875 = false ∨ valuation q 881 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (877)) (literal (valuationOf q) (885)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 1 (meaning877 q) (meaning885 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 885 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (878)) (literal (valuationOf q) (886)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 2 (meaning878 q) (meaning886 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 886 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (879)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 3 (meaning879 q) (meaning887 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 887 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (880)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 4 (meaning880 q) (meaning888 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 888 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 5 (meaning881 q) (meaning889 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 889 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_left (literal (valuationOf q) (854)) (literal (valuationOf q) (885)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 1 (meaning854 q) (meaning885 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 885 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 877 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (877)) (literal (valuationOf q) (886)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 1 1 (meaning854 q) (meaning877 q) (meaning886 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 877 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 877 = false ∨ valuation q 886 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 878 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (878)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 1 2 (meaning854 q) (meaning878 q) (meaning887 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 878 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 878 = false ∨ valuation q 887 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 879 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (879)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 1 3 (meaning854 q) (meaning879 q) (meaning888 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 879 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 879 = false ∨ valuation q 888 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 880 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (880)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 1 4 (meaning854 q) (meaning880 q) (meaning889 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 880 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 880 = false ∨ valuation q 889 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 881 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (881)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 1 5 (meaning854 q) (meaning881 q) (meaning890 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 881 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 881 = false ∨ valuation q 890 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_left (literal (valuationOf q) (855)) (literal (valuationOf q) (886)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 2 (meaning855 q) (meaning886 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 886 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 877 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (877)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 2 1 (meaning855 q) (meaning877 q) (meaning887 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 877 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 877 = false ∨ valuation q 887 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 878 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (878)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 2 2 (meaning855 q) (meaning878 q) (meaning888 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 878 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 878 = false ∨ valuation q 888 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 879 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (879)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 2 3 (meaning855 q) (meaning879 q) (meaning889 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 879 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 879 = false ∨ valuation q 889 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 880 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (880)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 2 4 (meaning855 q) (meaning880 q) (meaning890 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 880 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 880 = false ∨ valuation q 890 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 881 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (881)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 2 5 (meaning855 q) (meaning881 q) (meaning891 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 881 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 881 = false ∨ valuation q 891 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_left (literal (valuationOf q) (856)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 3 (meaning856 q) (meaning887 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 887 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 877 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (877)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 3 1 (meaning856 q) (meaning877 q) (meaning888 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 877 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 877 = false ∨ valuation q 888 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 878 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (878)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 3 2 (meaning856 q) (meaning878 q) (meaning889 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 878 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 878 = false ∨ valuation q 889 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 879 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (879)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 3 3 (meaning856 q) (meaning879 q) (meaning890 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 879 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 879 = false ∨ valuation q 890 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 880 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (880)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 3 4 (meaning856 q) (meaning880 q) (meaning891 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 880 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 880 = false ∨ valuation q 891 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 4 (meaning857 q) (meaning888 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 888 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 877 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (877)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 4 1 (meaning857 q) (meaning877 q) (meaning889 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 877 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 877 = false ∨ valuation q 889 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 878 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (878)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 4 2 (meaning857 q) (meaning878 q) (meaning890 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 878 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 878 = false ∨ valuation q 890 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 879 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -36, -38, -39, -42]) + (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -36, -38, -39, -42]) (l₂ := [-44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (879)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -36, -38, -39, -42]) (countLit q [-44, -46, -48, -50, -52, -55, -57, -60]) (count885 q) 4 3 (meaning857 q) (meaning879 q) (meaning891 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 879 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 879 = false ∨ valuation q 891 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 904 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (904)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 5 (meaning889 q) (meaning904 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 904 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 887 = false ∨ valuationOf q 903 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (887)) (literal (valuationOf q) (903)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 1 3 (meaning827 q) (meaning887 q) (meaning903 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 887 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 887 = false ∨ valuation q 903 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 888 = false ∨ valuationOf q 904 = true := by
  have hs : count900 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) + (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (l₂ := [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (888)) (literal (valuationOf q) (904)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]) (countLit q [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (count900 q) 1 4 (meaning827 q) (meaning888 q) (meaning904 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 888 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 888 = false ∨ valuation q 904 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E259.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112259
