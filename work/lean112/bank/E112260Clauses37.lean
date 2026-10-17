import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (869)) (countLit q [-15]) (countLit q [-16]) (count869 q) 1 (meaningNeg15 q) (meaning869 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 869 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 16 = true ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (870)) (countLit q [-15]) (countLit q [-16]) (count869 q) 1 1 (meaningNeg15 q) (meaningNeg16 q) (meaning870 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 870 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (871)) (countLit q [-20]) (countLit q [-21]) (count871 q) 1 (meaningNeg21 q) (meaning871 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 871 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (871)) (countLit q [-20]) (countLit q [-21]) (count871 q) 1 (meaningNeg20 q) (meaning871 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 871 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (872)) (countLit q [-20]) (countLit q [-21]) (count871 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning872 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 872 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 1 (meaning871 q) (meaning873 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 2 (meaning872 q) (meaning874 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (873)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 1 (meaning869 q) (meaning873 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 873 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (871)) (literal (valuationOf q) (874)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 1 1 (meaning869 q) (meaning871 q) (meaning874 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 871 = false ∨ valuation q 874 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (872)) (literal (valuationOf q) (875)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 1 2 (meaning869 q) (meaning872 q) (meaning875 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 872 = false ∨ valuation q 875 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (870)) (literal (valuationOf q) (874)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 2 (meaning870 q) (meaning874 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 874 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 2 1 (meaning870 q) (meaning871 q) (meaning875 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 871 = false ∨ valuation q 875 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count873 q = (countLit q [-15, -16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-15, -16]) (countLit q [-20, -21]) (count873 q) 2 2 (meaning870 q) (meaning872 q) (meaning876 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 872 = false ∨ valuation q 876 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (877)) (countLit q [-24]) (countLit q [-26]) (count877 q) 1 (meaningNeg26 q) (meaning877 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 877 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (877)) (countLit q [-24]) (countLit q [-26]) (count877 q) 1 (meaningNeg24 q) (meaning877 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 877 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 26 = true ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (878)) (countLit q [-24]) (countLit q [-26]) (count877 q) 1 1 (meaningNeg24 q) (meaningNeg26 q) (meaning878 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 878 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (879)) (countLit q [-28]) (countLit q [-30]) (count879 q) 1 (meaningNeg30 q) (meaning879 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 879 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (879)) (countLit q [-28]) (countLit q [-30]) (count879 q) 1 (meaningNeg28 q) (meaning879 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 879 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 30 = true ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (880)) (countLit q [-28]) (countLit q [-30]) (count879 q) 1 1 (meaningNeg28 q) (meaningNeg30 q) (meaning880 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 880 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (879)) (literal (valuationOf q) (881)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 1 (meaning879 q) (meaning881 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 881 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (880)) (literal (valuationOf q) (882)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 2 (meaning880 q) (meaning882 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 882 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (877)) (literal (valuationOf q) (881)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 1 (meaning877 q) (meaning881 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 881 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 879 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (879)) (literal (valuationOf q) (882)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 1 1 (meaning877 q) (meaning879 q) (meaning882 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 879 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 879 = false ∨ valuation q 882 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 880 = false ∨ valuationOf q 883 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (880)) (literal (valuationOf q) (883)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 1 2 (meaning877 q) (meaning880 q) (meaning883 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 880 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 880 = false ∨ valuation q 883 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (878)) (literal (valuationOf q) (882)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 2 (meaning878 q) (meaning882 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 882 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 879 = false ∨ valuationOf q 883 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (879)) (literal (valuationOf q) (883)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 2 1 (meaning878 q) (meaning879 q) (meaning883 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 879 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 879 = false ∨ valuation q 883 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 880 = false ∨ valuationOf q 884 = true := by
  have hs : count881 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (880)) (literal (valuationOf q) (884)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count881 q) 2 2 (meaning878 q) (meaning880 q) (meaning884 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 880 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 880 = false ∨ valuation q 884 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (885)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 1 (meaning881 q) (meaning885 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 885 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (886)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 2 (meaning882 q) (meaning886 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 886 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (883)) (literal (valuationOf q) (887)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 3 (meaning883 q) (meaning887 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 887 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (884)) (literal (valuationOf q) (888)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 4 (meaning884 q) (meaning888 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 888 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (873)) (literal (valuationOf q) (885)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 1 (meaning873 q) (meaning885 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 885 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E260.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112260
