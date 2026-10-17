import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 881 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (881)) (literal (valuationOf q) (886)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 1 1 (meaning873 q) (meaning881 q) (meaning886 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 881 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 881 = false ∨ valuation q 886 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 882 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (882)) (literal (valuationOf q) (887)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 1 2 (meaning873 q) (meaning882 q) (meaning887 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 882 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 882 = false ∨ valuation q 887 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (883)) (literal (valuationOf q) (888)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 1 3 (meaning873 q) (meaning883 q) (meaning888 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 883 = false ∨ valuation q 888 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (884)) (literal (valuationOf q) (889)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 1 4 (meaning873 q) (meaning884 q) (meaning889 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 884 = false ∨ valuation q 889 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (874)) (literal (valuationOf q) (886)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 2 (meaning874 q) (meaning886 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 886 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 881 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (881)) (literal (valuationOf q) (887)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 2 1 (meaning874 q) (meaning881 q) (meaning887 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 881 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 881 = false ∨ valuation q 887 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 882 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (882)) (literal (valuationOf q) (888)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 2 2 (meaning874 q) (meaning882 q) (meaning888 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 882 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 882 = false ∨ valuation q 888 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (883)) (literal (valuationOf q) (889)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 2 3 (meaning874 q) (meaning883 q) (meaning889 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 883 = false ∨ valuation q 889 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (884)) (literal (valuationOf q) (890)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 2 4 (meaning874 q) (meaning884 q) (meaning890 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 884 = false ∨ valuation q 890 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (875)) (literal (valuationOf q) (887)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 3 (meaning875 q) (meaning887 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 887 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 881 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (881)) (literal (valuationOf q) (888)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 3 1 (meaning875 q) (meaning881 q) (meaning888 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 881 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 881 = false ∨ valuation q 888 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 882 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (882)) (literal (valuationOf q) (889)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 3 2 (meaning875 q) (meaning882 q) (meaning889 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 882 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 882 = false ∨ valuation q 889 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (883)) (literal (valuationOf q) (890)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 3 3 (meaning875 q) (meaning883 q) (meaning890 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 883 = false ∨ valuation q 890 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (884)) (literal (valuationOf q) (891)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 3 4 (meaning875 q) (meaning884 q) (meaning891 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 884 = false ∨ valuation q 891 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (876)) (literal (valuationOf q) (888)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 4 (meaning876 q) (meaning888 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 888 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 881 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (881)) (literal (valuationOf q) (889)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 4 1 (meaning876 q) (meaning881 q) (meaning889 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 881 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 881 = false ∨ valuation q 889 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 882 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (882)) (literal (valuationOf q) (890)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 4 2 (meaning876 q) (meaning882 q) (meaning890 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 882 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 882 = false ∨ valuation q 890 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-15, -16, -20, -21]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -20, -21]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (literal (valuationOf q) (891)) (countLit q [-15, -16, -20, -21]) (countLit q [-24, -26, -28, -30]) (count885 q) 4 3 (meaning876 q) (meaning883 q) (meaning891 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 883 = false ∨ valuation q 891 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (885)) (literal (valuationOf q) (893)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 (meaning885 q) (meaning893 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 893 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (886)) (literal (valuationOf q) (894)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 (meaning886 q) (meaning894 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 894 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (887)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 3 (meaning887 q) (meaning895 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 895 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (888)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 4 (meaning888 q) (meaning896 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 896 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 5 (meaning889 q) (meaning897 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 897 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (890)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 6 (meaning890 q) (meaning898 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 898 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (862)) (literal (valuationOf q) (893)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 (meaning862 q) (meaning893 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 893 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 885 = false ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (885)) (literal (valuationOf q) (894)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 1 (meaning862 q) (meaning885 q) (meaning894 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 885 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 885 = false ∨ valuation q 894 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 886 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (886)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 2 (meaning862 q) (meaning886 q) (meaning895 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 886 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 886 = false ∨ valuation q 895 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 887 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (887)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 3 (meaning862 q) (meaning887 q) (meaning896 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 887 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 887 = false ∨ valuation q 896 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (888)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 4 (meaning862 q) (meaning888 q) (meaning897 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 888 = false ∨ valuation q 897 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (889)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 5 (meaning862 q) (meaning889 q) (meaning898 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 889 = false ∨ valuation q 898 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (890)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 6 (meaning862 q) (meaning890 q) (meaning899 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 890 = false ∨ valuation q 899 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (891)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 1 7 (meaning862 q) (meaning891 q) (meaning900 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 891 = false ∨ valuation q 900 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E260.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112260
