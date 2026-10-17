import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (855)) (literal (valuationOf q) (886)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 (meaning855 q) (meaning886 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 886 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 877 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (877)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 1 (meaning855 q) (meaning877 q) (meaning887 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 877 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 877 = false ∨ valuation q 887 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 878 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (878)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 2 (meaning855 q) (meaning878 q) (meaning888 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 878 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 878 = false ∨ valuation q 888 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 879 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (879)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 3 (meaning855 q) (meaning879 q) (meaning889 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 879 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 879 = false ∨ valuation q 889 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 880 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (880)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 4 (meaning855 q) (meaning880 q) (meaning890 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 880 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 880 = false ∨ valuation q 890 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 881 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (881)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 5 (meaning855 q) (meaning881 q) (meaning891 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 881 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 881 = false ∨ valuation q 891 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 882 = false ∨ valuationOf q 892 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (882)) (literal (valuationOf q) (892)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 6 (meaning855 q) (meaning882 q) (meaning892 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 882 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 882 = false ∨ valuation q 892 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (856)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 (meaning856 q) (meaning887 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 887 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 877 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (877)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 1 (meaning856 q) (meaning877 q) (meaning888 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 877 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 877 = false ∨ valuation q 888 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 878 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (878)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 2 (meaning856 q) (meaning878 q) (meaning889 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 878 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 878 = false ∨ valuation q 889 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 879 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (879)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 3 (meaning856 q) (meaning879 q) (meaning890 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 879 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 879 = false ∨ valuation q 890 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 880 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (880)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 4 (meaning856 q) (meaning880 q) (meaning891 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 880 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 880 = false ∨ valuation q 891 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 881 = false ∨ valuationOf q 892 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (881)) (literal (valuationOf q) (892)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 5 (meaning856 q) (meaning881 q) (meaning892 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 881 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 881 = false ∨ valuation q 892 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 882 = false ∨ valuationOf q 893 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (882)) (literal (valuationOf q) (893)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 6 (meaning856 q) (meaning882 q) (meaning893 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 882 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 882 = false ∨ valuation q 893 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 4 (meaning857 q) (meaning888 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 888 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 877 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (877)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 4 1 (meaning857 q) (meaning877 q) (meaning889 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 877 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 877 = false ∨ valuation q 889 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 878 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (878)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 4 2 (meaning857 q) (meaning878 q) (meaning890 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 878 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 878 = false ∨ valuation q 890 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 879 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (879)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 4 3 (meaning857 q) (meaning879 q) (meaning891 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 879 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 879 = false ∨ valuation q 891 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 880 = false ∨ valuationOf q 892 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (880)) (literal (valuationOf q) (892)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 4 4 (meaning857 q) (meaning880 q) (meaning892 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 880 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 880 = false ∨ valuation q 892 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 881 = false ∨ valuationOf q 893 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (881)) (literal (valuationOf q) (893)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 4 5 (meaning857 q) (meaning881 q) (meaning893 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 881 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 881 = false ∨ valuation q 893 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (858)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 5 (meaning858 q) (meaning889 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 889 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 877 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (877)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 5 1 (meaning858 q) (meaning877 q) (meaning890 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 877 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 877 = false ∨ valuation q 890 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 878 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (878)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 5 2 (meaning858 q) (meaning878 q) (meaning891 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 878 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 878 = false ∨ valuation q 891 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 879 = false ∨ valuationOf q 892 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (879)) (literal (valuationOf q) (892)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 5 3 (meaning858 q) (meaning879 q) (meaning892 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 879 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 879 = false ∨ valuation q 892 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 880 = false ∨ valuationOf q 893 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (880)) (literal (valuationOf q) (893)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 5 4 (meaning858 q) (meaning880 q) (meaning893 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 880 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 880 = false ∨ valuation q 893 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 877 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (859)) (literal (valuationOf q) (877)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 6 1 (meaning859 q) (meaning877 q) (meaning891 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 877 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 877 = false ∨ valuation q 891 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 892 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) + (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (l₂ := [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (892)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (count900 q) 1 8 (meaning827 q) (meaning892 q) (meaning908 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 892 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 892 = false ∨ valuation q 908 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 888 = false ∨ valuationOf q 905 = true := by
  have hs : count900 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) + (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (l₂ := [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (888)) (literal (valuationOf q) (905)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (count900 q) 2 4 (meaning828 q) (meaning888 q) (meaning905 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 888 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 888 = false ∨ valuation q 905 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 891 = false ∨ valuationOf q 908 = true := by
  have hs : count900 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) + (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (l₂ := [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (891)) (literal (valuationOf q) (908)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (count900 q) 2 7 (meaning828 q) (meaning891 q) (meaning908 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 891 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 891 = false ∨ valuation q 908 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 892 = false ∨ valuationOf q 909 = true := by
  have hs : count900 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) + (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (l₂ := [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (892)) (literal (valuationOf q) (909)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (count900 q) 2 8 (meaning828 q) (meaning892 q) (meaning909 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 892 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 892 = false ∨ valuation q 909 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 888 = false ∨ valuationOf q 906 = true := by
  have hs : count900 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) + (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (l₂ := [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (888)) (literal (valuationOf q) (906)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (count900 q) 3 4 (meaning829 q) (meaning888 q) (meaning906 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 888 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 888 = false ∨ valuation q 906 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 889 = false ∨ valuationOf q 907 = true := by
  have hs : count900 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) + (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (l₂ := [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (889)) (literal (valuationOf q) (907)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28]) (countLit q [-30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (count900 q) 3 5 (meaning829 q) (meaning889 q) (meaning907 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 889 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 889 = false ∨ valuation q 907 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E257.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112257
