import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (877)) (countLit q [-23]) (countLit q [-25]) (count877 q) 1 (meaningNeg25 q) (meaning877 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 877 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (877)) (countLit q [-23]) (countLit q [-25]) (count877 q) 1 (meaningNeg23 q) (meaning877 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 877 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 25 = true ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (878)) (countLit q [-23]) (countLit q [-25]) (count877 q) 1 1 (meaningNeg23 q) (meaningNeg25 q) (meaning878 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 25 = true ∨ valuation q 878 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (879)) (countLit q [-28]) (countLit q [-30]) (count879 q) 1 (meaningNeg30 q) (meaning879 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 879 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (879)) (countLit q [-28]) (countLit q [-30]) (count879 q) 1 (meaningNeg28 q) (meaning879 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 879 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 30 = true ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (880)) (countLit q [-28]) (countLit q [-30]) (count879 q) 1 1 (meaningNeg28 q) (meaningNeg30 q) (meaning880 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 880 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (879)) (literal (valuationOf q) (881)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 1 (meaning879 q) (meaning881 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 881 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (880)) (literal (valuationOf q) (882)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 2 (meaning880 q) (meaning882 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 882 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (877)) (literal (valuationOf q) (881)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 1 (meaning877 q) (meaning881 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 881 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 879 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (879)) (literal (valuationOf q) (882)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 1 1 (meaning877 q) (meaning879 q) (meaning882 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 879 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 879 = false ∨ valuation q 882 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 880 = false ∨ valuationOf q 883 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (880)) (literal (valuationOf q) (883)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 1 2 (meaning877 q) (meaning880 q) (meaning883 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 880 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 880 = false ∨ valuation q 883 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (878)) (literal (valuationOf q) (882)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 2 (meaning878 q) (meaning882 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 882 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 879 = false ∨ valuationOf q 883 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (879)) (literal (valuationOf q) (883)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 2 1 (meaning878 q) (meaning879 q) (meaning883 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 879 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 879 = false ∨ valuation q 883 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 880 = false ∨ valuationOf q 884 = true := by
  have hs : count881 q = (countLit q [-23, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (880)) (literal (valuationOf q) (884)) (countLit q [-23, -25]) (countLit q [-28, -30]) (count881 q) 2 2 (meaning878 q) (meaning880 q) (meaning884 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 880 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 880 = false ∨ valuation q 884 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (885)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 1 (meaning881 q) (meaning885 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 885 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (886)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 2 (meaning882 q) (meaning886 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 886 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (883)) (literal (valuationOf q) (887)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 3 (meaning883 q) (meaning887 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 887 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (884)) (literal (valuationOf q) (888)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 4 (meaning884 q) (meaning888 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 888 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (873)) (literal (valuationOf q) (885)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 1 (meaning873 q) (meaning885 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 885 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 881 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (881)) (literal (valuationOf q) (886)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 1 1 (meaning873 q) (meaning881 q) (meaning886 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 881 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 881 = false ∨ valuation q 886 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 882 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (882)) (literal (valuationOf q) (887)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 1 2 (meaning873 q) (meaning882 q) (meaning887 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 882 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 882 = false ∨ valuation q 887 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (883)) (literal (valuationOf q) (888)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 1 3 (meaning873 q) (meaning883 q) (meaning888 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 883 = false ∨ valuation q 888 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (884)) (literal (valuationOf q) (889)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 1 4 (meaning873 q) (meaning884 q) (meaning889 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 884 = false ∨ valuation q 889 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (874)) (literal (valuationOf q) (886)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 2 (meaning874 q) (meaning886 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 886 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 881 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (881)) (literal (valuationOf q) (887)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 2 1 (meaning874 q) (meaning881 q) (meaning887 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 881 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 881 = false ∨ valuation q 887 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 882 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (882)) (literal (valuationOf q) (888)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 2 2 (meaning874 q) (meaning882 q) (meaning888 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 882 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 882 = false ∨ valuation q 888 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (883)) (literal (valuationOf q) (889)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 2 3 (meaning874 q) (meaning883 q) (meaning889 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 883 = false ∨ valuation q 889 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (884)) (literal (valuationOf q) (890)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 2 4 (meaning874 q) (meaning884 q) (meaning890 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 884 = false ∨ valuation q 890 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (875)) (literal (valuationOf q) (887)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 3 (meaning875 q) (meaning887 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 887 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 881 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (881)) (literal (valuationOf q) (888)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 3 1 (meaning875 q) (meaning881 q) (meaning888 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 881 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 881 = false ∨ valuation q 888 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 882 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (882)) (literal (valuationOf q) (889)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 3 2 (meaning875 q) (meaning882 q) (meaning889 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 882 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 882 = false ∨ valuation q 889 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (883)) (literal (valuationOf q) (890)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 3 3 (meaning875 q) (meaning883 q) (meaning890 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 883 = false ∨ valuation q 890 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E256.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112256
