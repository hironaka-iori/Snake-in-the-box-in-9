import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 877 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (877)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 1 3 (meaning867 q) (meaning877 q) (meaning882 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 877 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 877 = false ∨ valuation q 882 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 878 = false ∨ valuationOf q 883 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (878)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 1 4 (meaning867 q) (meaning878 q) (meaning883 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 878 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 878 = false ∨ valuation q 883 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (868)) (literal (valuationOf q) (880)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 2 (meaning868 q) (meaning880 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 880 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (875)) (literal (valuationOf q) (881)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 2 1 (meaning868 q) (meaning875 q) (meaning881 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 875 = false ∨ valuation q 881 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (876)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 2 2 (meaning868 q) (meaning876 q) (meaning882 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 876 = false ∨ valuation q 882 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 877 = false ∨ valuationOf q 883 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (877)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 2 3 (meaning868 q) (meaning877 q) (meaning883 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 877 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 877 = false ∨ valuation q 883 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 878 = false ∨ valuationOf q 884 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (878)) (literal (valuationOf q) (884)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 2 4 (meaning868 q) (meaning878 q) (meaning884 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 878 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 878 = false ∨ valuation q 884 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (881)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 3 (meaning869 q) (meaning881 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 881 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 875 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (875)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 3 1 (meaning869 q) (meaning875 q) (meaning882 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 875 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 875 = false ∨ valuation q 882 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 876 = false ∨ valuationOf q 883 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 3 2 (meaning869 q) (meaning876 q) (meaning883 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 876 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 876 = false ∨ valuation q 883 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 877 = false ∨ valuationOf q 884 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (877)) (literal (valuationOf q) (884)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 3 3 (meaning869 q) (meaning877 q) (meaning884 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 877 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 877 = false ∨ valuation q 884 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 878 = false ∨ valuationOf q 885 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (878)) (literal (valuationOf q) (885)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 3 4 (meaning869 q) (meaning878 q) (meaning885 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 878 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 878 = false ∨ valuation q 885 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (870)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 4 (meaning870 q) (meaning882 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 882 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 875 = false ∨ valuationOf q 883 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (875)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 4 1 (meaning870 q) (meaning875 q) (meaning883 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 875 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 875 = false ∨ valuation q 883 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 876 = false ∨ valuationOf q 884 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (876)) (literal (valuationOf q) (884)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 4 2 (meaning870 q) (meaning876 q) (meaning884 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 876 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 876 = false ∨ valuation q 884 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 877 = false ∨ valuationOf q 885 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (877)) (literal (valuationOf q) (885)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 4 3 (meaning870 q) (meaning877 q) (meaning885 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 877 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 877 = false ∨ valuation q 885 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 878 = false ∨ valuationOf q 886 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (878)) (literal (valuationOf q) (886)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 4 4 (meaning870 q) (meaning878 q) (meaning886 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 878 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 878 = false ∨ valuation q 886 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (887)) (countLit q [-15]) (countLit q [-19]) (count887 q) 1 (meaningNeg19 q) (meaning887 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 887 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (887)) (countLit q [-15]) (countLit q [-19]) (count887 q) 1 (meaningNeg15 q) (meaning887 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 887 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 19 = true ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (888)) (countLit q [-15]) (countLit q [-19]) (count887 q) 1 1 (meaningNeg15 q) (meaningNeg19 q) (meaning888 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 888 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 889 = true := by
  have hs : count889 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (889)) (countLit q [-22]) (countLit q [-24]) (count889 q) 1 (meaningNeg24 q) (meaning889 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 889 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 889 = true := by
  have hs : count889 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (889)) (countLit q [-22]) (countLit q [-24]) (count889 q) 1 (meaningNeg22 q) (meaning889 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 889 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 24 = true ∨ valuationOf q 890 = true := by
  have hs : count889 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (890)) (countLit q [-22]) (countLit q [-24]) (count889 q) 1 1 (meaningNeg22 q) (meaningNeg24 q) (meaning890 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 890 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (891)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 1 (meaning889 q) (meaning891 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 891 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_right (literal (valuationOf q) (890)) (literal (valuationOf q) (892)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 2 (meaning890 q) (meaning892 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 892 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_left (literal (valuationOf q) (887)) (literal (valuationOf q) (891)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 1 (meaning887 q) (meaning891 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 891 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 889 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (889)) (literal (valuationOf q) (892)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 1 1 (meaning887 q) (meaning889 q) (meaning892 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 889 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 889 = false ∨ valuation q 892 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 890 = false ∨ valuationOf q 893 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (890)) (literal (valuationOf q) (893)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 1 2 (meaning887 q) (meaning890 q) (meaning893 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 890 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 890 = false ∨ valuation q 893 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_left (literal (valuationOf q) (888)) (literal (valuationOf q) (892)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 2 (meaning888 q) (meaning892 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 892 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 889 = false ∨ valuationOf q 893 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_two (literal (valuationOf q) (888)) (literal (valuationOf q) (889)) (literal (valuationOf q) (893)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 2 1 (meaning888 q) (meaning889 q) (meaning893 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 889 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 889 = false ∨ valuation q 893 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 890 = false ∨ valuationOf q 894 = true := by
  have hs : count891 q = (countLit q [-15, -19]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -19]) (l₂ := [-22, -24])
  have hm := merge_two (literal (valuationOf q) (888)) (literal (valuationOf q) (890)) (literal (valuationOf q) (894)) (countLit q [-15, -19]) (countLit q [-22, -24]) (count891 q) 2 2 (meaning888 q) (meaning890 q) (meaning894 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 890 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 890 = false ∨ valuation q 894 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (895)) (countLit q [-25]) (countLit q [-27]) (count895 q) 1 (meaningNeg27 q) (meaning895 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 895 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E121.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112121
